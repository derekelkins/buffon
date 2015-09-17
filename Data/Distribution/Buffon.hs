{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}

-- From "On Buffon Machines and Numbers" by Flajolet, Pelletier, and Soria

module Data.Distribution.Buffon (
    Buffon, runBuffon, runBuffonWithSystemRandomT,
    toss, third, toNumberWith, toNumberM, toNumber,
    expectationWith, expectationM, expectation,
    bernoulli, if_, mean, evenParity, geometric,
    vonNeumann, polylogarithmic, polylogarithmic',
    poisson, poisson', anotherPoisson, logarithmic, logarithmic',
    alternating, evenAlternating, oddAlternating,
    isAlternating, cosine, sine, cotangent, bump, erf,
    ternary, binary, ternaryBistoch, Bistoch, Bistoch',
    fromBistoch, fromBistoch', bistoch, integrate', arcsin,
    squareRoot, ramanujan, arctan, integrate, createReal,
    pi8, pi4, zeta3
  ) where
import Control.Monad.IO.Class ( MonadIO )
import Control.Monad.Primitive ( PrimMonad )
import Control.Monad.Primitive.Class ( MonadPrim(..) )
import Control.Monad.ST (ST, runST)
import Control.Monad.Trans.Class ( MonadTrans )
import Data.Bits ( testBit )
import Data.Function ( fix )
import Data.Word ( Word64 )
import System.Random.MWC ( Variate )
import System.Random.MWC.Monad ( uniform, Rand, runWithCreate, runWithSystemRandomT )

newtype Buffon m a = Buffon { unBuffon :: Rand m a }
    deriving (Functor, Applicative, Monad, MonadIO, MonadTrans)

instance (PrimMonad m, MonadPrim m) => MonadPrim (Buffon m) where
    type BasePrimMonad (Buffon m) = BasePrimMonad m
    liftPrim = Buffon . liftPrim

runBuffon :: MonadPrim m => Buffon m a -> m a
runBuffon = runWithCreate . unBuffon

runBuffonWithSystemRandomT :: (MonadPrim m, BasePrimMonad m ~ IO) => Buffon m a -> m a
runBuffonWithSystemRandomT = runWithSystemRandomT . unBuffon

----

-- | Toss a coin.  P(toss) = 1/2
toss :: (MonadPrim m) => Buffon m Bool
toss = Buffon uniform

-- | A biased coin. P(third) = 1/3
third :: (MonadPrim m) => Buffon m Bool
third = do
    a <- toss
    b <- toss
    if a && b then third else return (not (a||b))

toNumberWith :: (Fractional n, MonadPrim m) => Int -> Buffon m Bool -> m n
toNumberWith n p = runBuffon (go n 0)
    where go 0 !acc = return (acc/fromIntegral n)
          go c acc = if_ p (go (c-1) (acc+1)) (go (c-1) acc)

toNumberWithSystemRandomT :: (Fractional n) => Int -> Buffon IO Bool -> IO n
toNumberWithSystemRandomT n p = runBuffonWithSystemRandomT (go n 0)
    where go 0 !acc = return (acc/fromIntegral n)
          go c acc = if_ p (go (c-1) (acc+1)) (go (c-1) acc)

toNumberM :: (Fractional n, MonadPrim m) => Buffon m Bool -> m n
toNumberM = toNumberWith 1000000

-- | Estimate the probability of getting True
toNumber :: (Fractional n) => (forall s. Buffon (ST s) Bool) -> n
toNumber p = runST (toNumberM p)

expectationWith :: (Integral a, Fractional n, MonadPrim m) => Int -> Buffon m a -> m n
expectationWith n p = runBuffon (go n 0)
    where go 0 !acc = return (fromIntegral acc/fromIntegral n)
          go c acc = do x <- p; go (c-1) (acc+x)

expectationM :: (Integral a, Fractional n, MonadPrim m) => Buffon m a -> m n
expectationM = expectationWith 1000000

-- | Estimate the expectation
expectation :: (Integral a, Fractional n) => (forall s. Buffon (ST s) a) -> n
expectation p = runST (expectationM p)

----

--  If P(p) = x then p = bernoulli x
-- bernoulli x = fmap (\n -> bits x !! (n+1) == 1) (geometric toss)
--  where bits x returns the bits of the binary expansion of x

-- Cheating bernoulli
-- | P(bernoulli x) = x
bernoulli :: (Ord n, Variate n, Fractional n, MonadPrim m) => n -> Buffon m Bool
bernoulli p = do
    x <- Buffon uniform
    if x <= p then 1 else 0

-- | P(if_ (bernoulli r) (bernoulli p) (bernoulli q)) = rp + (1-r)q
if_ :: (MonadPrim m) => Buffon m Bool -> Buffon m a -> Buffon m a -> Buffon m a
if_ r p q = do b <- r; if b then p else q

-- | P(mean (bernoulli p) (bernoulli q)) = (p+q)/2
mean :: (MonadPrim m) => Buffon m a -> Buffon m a -> Buffon m a
mean p q = if_ toss p q

instance Eq (Buffon m a) where (==) = error "(==) not defined for Buffon"

instance Show (Buffon m a) where show _ = "<buffon>"

-- Warning: These don't obey the laws you'd expect.
-- They are left-biased insofar as:
-- fix (\p -> p*q) == undefined regardless of q (same for +)
-- Practically, this means you want left associated uses of * and +.
instance (MonadPrim m) => Num (Buffon m Bool) where
    p * q = if_ q p 0            -- | P(bernoulli p*bernoulli q) = pq
    p + q = if_ q 1 p            -- | P(bernoulli p+bernoulli q) = p + q - pq
    negate p = not <$> p         -- | P(-bernoulli p)  = 1 - p
    fromInteger 0 = return False -- | P(0)   = 0
    fromInteger 1 = return True  -- | P(1)   = 1
    abs = error "abs not defined for Buffon"
    signum = error "signum not defined for Buffon"

----

-- | P(evenParity (bernoulli p)) = 1/(1+p)
evenParity :: (MonadPrim m) => Buffon m Bool -> Buffon m Bool
evenParity p = fix (\q -> if_ p (if_ p q 0) 1)

-- | von Neumann schema
-- |
-- | Let Perms be a subset of the class of all permutations.
-- | Let F_n be the number of permutations of n items in Perms.
-- | Define F(z) = sum_(n>=0) F_n z^n/n!, i.e. the exponential generating function.
-- | Let U = (U_1, ..., U_n) be a vector of bit streams.
-- | Let type(U) be the permutation that sorts U.  type(U) is the order type of U.
-- | The von Neumann schema is:
-- |
-- | vonNeumann[Perms] p = go 1
-- |    where go k = do
-- |            n <- geometric p
-- |            let U be an n-vector of uniformly distributed bit streams
-- |            if type(U) in Perms then return (n, k) else go (k+1)
-- |
-- | P(fst (vonNeumann[Perms] (bernoulli p)) == n) = F_n/F(p) p^n/n!
-- | s = (1-p)F(p)
-- | P(snd (vonNeumann[Perms] (bernoulli p)) == k) = s(1-s)^(k-1)
-- | sum_(k>=1) k P(snd (vonNeumann[Perms] (bernoulli p)) == k) = 1/s
-- | The actual function takes a function inClass such that P(inClass n) = F_n/n!
vonNeumann :: (MonadPrim m) => (Int -> Buffon m Bool) -> Buffon m Bool -> Buffon m (Int, Int)
vonNeumann inClass p = go 1
    where go !k = do
            n <- geometric p
            if_ (inClass n) (return (n,k)) (go (k+1))

-- | P(geometric (bernoulli p) == r) = (1-p)p^r
-- | Fits the von Neumann schema with F(z) = 1/(1-z) (i.e. Perms = all permutations)
geometric :: (MonadPrim m) => Buffon m Bool -> Buffon m Int
geometric p = go 0
    where go !acc = if_ p (go (acc+1)) (return acc)

-- | P(fst (poisson (bernoulli p)) == r) = exp(-p)p^r/r!
-- | Fits the von Neumann schema with F(z) = exp(z) (i.e. Perms = sorted permutations)
-- Note: P(liftM2 (+) (fst (poisson (bernoulli p))) (fst (poisson (bernoulli q))) == r) = exp(-p-q)(p+q)^r/r!
poisson :: (MonadPrim m) => Buffon m Bool -> Buffon m (Int, Int)
poisson = vonNeumann isSorted
    where isSorted 0 = return True
          isSorted 1 = 1
          isSorted i = loopFalse 0
            where loopFalse j | j < i     = mean (loopTrue j (j+1)) (loopFalse (j+1))
                              | otherwise = isSorted i
                  loopTrue cut j | j < i     = mean (loopTrue cut (j+1)) 0
                                 | otherwise = isSorted cut * isSorted (i-cut)

anotherPoisson :: (MonadPrim m) => Buffon m Bool -> Buffon m (Int, Int)
anotherPoisson = vonNeumann isSorted
    where bernoullis = map (bernoulli . recip) [2 :: Double ..]
          isSorted n = product (take (n-1) bernoullis)

-- | P(poisson' (bernoulli p)) = exp(-p) = P(fst (poisson (bernoulli p)) == 0)
poisson' :: (MonadPrim m) => Buffon m Bool -> Buffon m Bool
poisson' = fmap ((0==) . fst) . poisson

-- | P(fst (logarithmic (bernoulli p)) == r) = -p^r/(rlog(1-p))
-- | Fits the von Neumann schema with F(z) = -log(1-z) (i.e. Perms = cyclic permutations)
logarithmic :: (MonadPrim m) => Buffon m Bool -> Buffon m (Int, Int)
logarithmic = polylogarithmic 1

-- | P(logarithmic' (bernoulli p)) = -p/log(1-p) = P(fst (logarithmic (bernoulli p)) == 1)
logarithmic' :: (MonadPrim m) => Buffon m Bool -> Buffon m Bool
logarithmic' = fmap ((1==) . fst) . logarithmic

-- | P(fst (polylogarthmic k (bernoulli p)) == r) = p^r/(r^k li_k(p))
polylogarithmic :: (MonadPrim m) => Int -> Buffon m Bool -> Buffon m (Int, Int)
polylogarithmic r = vonNeumann (\n -> (isCyclic n)^r)
    where isCyclic 0 = return False
          isCyclic 1 = 1
          isCyclic i = do
              b <- toss
              let inner 0 !acc = isCyclic acc
                  inner j acc = do
                      b' <- toss
                      case compare b b' of
                          LT -> 0
                          EQ -> inner (j-1) (acc+1)
                          GT -> inner (j-1) acc
              inner (i-1) 1

-- | P(polylogarithmic' k (bernoulli p)) = p/li_k(p) = P(fst (polylogarithmic k (bernoulli p)) == 1)
polylogarithmic' :: (MonadPrim m) => Int -> Buffon m Bool -> Buffon m Bool
polylogarithmic' r = fmap ((1==) . fst) . polylogarithmic r

-- | P(fst (alternating (bernoulli p)) == r) = A_r/r! p^r/(sec(p)+tan(p)) = A_r/r! p^r/tan(z/2+pi/4)
-- | Fits the von Neumann schema with F(z) = sec(z) + tan(z) = tan(z/2+pi/4) (i.e. Perms = alternating permutations)
-- | For A_n see OEIS A000111 
alternating :: (MonadPrim m) => Buffon m Bool -> Buffon m (Int, Int)
alternating = vonNeumann (\n -> isAlternating False n [])

-- | P(fst (evenAlternating (bernoulli p)) == r) = A_r/r! p^r/sec(p) for even r, 0 otherwise
-- | Fits the von Neumann schema with F(z) = sec(z) (i.e. Perms = even length alternating permutations)
evenAlternating :: (MonadPrim m) => Buffon m Bool -> Buffon m (Int, Int)
evenAlternating = vonNeumann (\n -> if even n then isAlternating False n [] else 0)

-- | P(fst (oddAlternating (bernoulli p)) == r) = A_r/r! p^r/tan(p) for odd r, 0 otherwise
-- | Fits the von Neumann schema with F(z) = tan(z) (i.e. Perms = odd length alternating permutations)
oddAlternating :: (MonadPrim m) => Buffon m Bool -> Buffon m (Int, Int)
oddAlternating = vonNeumann (\n -> if odd n then isAlternating False n [] else 0)

isAlternating :: (MonadPrim m) => Bool -> Int -> [Bool] -> Buffon m Bool
isAlternating !_  0  _ = 1
isAlternating !_  1  _ = 1
isAlternating !p !i bs = walk bs [] -- is it better to reverse bs here or append in the calls?
    where walk [] acc = walk' acc
          walk (b:bs) acc = do
            b' <- toss
            case if p then compare b b' else compare b' b of
                LT -> 0
                EQ -> walk bs (b:acc)
                GT -> isAlternating (not p) (i-1) (acc++[b'])
          walk' acc = do
            b <- toss
            b' <- toss
            case compare b b' of
                LT -> 0
                EQ -> walk' (b':acc)
                GT -> isAlternating (not p) (i-1) (acc++[p==b'])

-- | P(cosine (bernoulli p)) = cos(p) = P(fst (evenAlternating (bernoulli p)) == 0)
cosine :: (MonadPrim m) => Buffon m Bool -> Buffon m Bool
cosine = fmap ((0==) . fst) . evenAlternating

-- | P(sine (bernoulli p)) = sin(p)
sine :: (MonadPrim m) => Buffon m Bool -> Buffon m Bool
sine p = squareRoot (-cosine p^2)

-- | P(cotangent (bernoulli p)) = pcot(p) = P(fst (oddAlternating (bernoulli p)) == 1)
cotangent :: (MonadPrim m) => Buffon m Bool -> Buffon m Bool
cotangent = fmap ((1==) . fst) . oddAlternating

-- | P(squareRoot (bernoulli p)) = sqrt(p)
squareRoot :: (MonadPrim m) => Buffon m Bool -> Buffon m Bool
squareRoot = bump 1 . negate

-- | P(bump t (bernoulli p)) = (1-p)S(p/2)
-- |    where S(z) = sum_(n>=0) ((t+1)n choose n) z^(tn+n)
bump :: (MonadPrim m) => Int -> Buffon m Bool -> Buffon m Bool
bump t p = go 0
    where go !c = if_ p (bump' (bump' go) c) (return (c==0))
          bump' k !c = mean (k (c+t)) (k (c-1))

-- | Bi(nary )stoch(astic) (grammar)
-- | Let G be a Bistoch' X.  It represents the following grammar:
-- | X_i = T (G X_i False) | H (G X_i True)
-- | where X_i is in X, the set of non-terminals and we sequence the list of results from g.
-- | See ternaryBistoch for an example.
type Bistoch k = k -> Bool -> [k]

-- | Bistoch ~ Bistoch'
type Bistoch' k = k -> ([k],[k])
                                       
fromBistoch' :: Bistoch' k -> Bistoch k
fromBistoch' g k False = fst (g k)
fromBistoch' g k True  = snd (g k)

fromBistoch :: Bistoch k -> Bistoch' k
fromBistoch g k = (g k False, g k True)

-- | ternaryBistoch = fromBistoch' $ \() -> ([], [(),(),()])
-- | Represents the grammar: X = T | H X X X
-- | This grammar corresponds to ternary trees.
ternaryBistoch :: Bistoch ()
ternaryBistoch = fromBistoch' $ \() -> ([], [(),(),()])

-- | P(ternary (bernoulli p)) = T(p/2) 
-- |    where 2T(p/2) = p(1+T(p/2)^3)
ternary :: (MonadPrim m) => Buffon m Bool -> Buffon m Bool
ternary = bistoch ternaryBistoch ()

-- | P(binary (bernoulli p)) = 1/p - sqrt(1/p^2 - 1)
binary :: (MonadPrim m) => Buffon m Bool -> Buffon m Bool
binary = bistoch (fromBistoch' $ \() -> ([], [(),()])) ()

-- | Sample from a binary stochastic grammar, g, with given starting non-terminal s.
-- | L(g;s) is the language generated by the grammar starting from non-terminal s.
-- | See the Chomsky-Schutzenberger theorem.
-- | (-p)*bistoch g s p = do
-- |    n <- geometric p
-- |    ws <- replicateM n toss
-- |    return (L(g;s) matches ws) 
-- | P(bistoch g s (bernoulli p)) = S(p/2)
-- |    where S(z) = sum_(n>=0) S_n z^n
-- |      and S_n are the number of words of length n matched by L(g;s).
bistoch :: (MonadPrim m) => Bistoch k -> k -> Buffon m Bool -> Buffon m Bool
bistoch g s p = matches [s] 1
    where matches     [] c = c
          matches (k:ks) c = (do
            ks' <- g k <$> toss
            matches ks' (matches ks c)) * p

-- | P(ramanujan) = 1/pi
ramanujan :: (MonadPrim m) => Buffon m Bool
ramanujan = do
    x1 <- geometric (toss*toss)
    x2 <- geometric (toss*toss)
    b <- bernoulli (5/9 :: Double)
    let t = 2*(if b then x1 + x2 + 1 else x1 + x2)
    let go 0 !c = return $ c == 0
        go i  c = mean (go (i-1) (c+1)) (go (i-1) (c-1))
    (go t 0 * go t 0) * go t 0

-- Close enough to a real...
-- We could save random bits by flipping on demand and caching the results but it doesn't seem worth it...
createReal :: (MonadPrim m) => Buffon m (Buffon m Bool)
createReal = do
    u <- Buffon uniform
    return (do
        n <- geometric toss
        return (testBit (u :: Word64) n))

-- | P(integrate f (bernoulli p)) = int_0^p f(w)dw/p
integrate' :: (MonadPrim m) => (Buffon m Bool -> Buffon m Bool) -> Buffon m Bool -> Buffon m Bool
integrate' f p = createReal >>= f . (p*)

-- | P(integrate f (bernoulli p)) = int_0^p f(w)dw
integrate :: (MonadPrim m) => (Buffon m Bool -> Buffon m Bool) -> Buffon m Bool -> Buffon m Bool
integrate f p = integrate' f p * p

-- | P(arctan (bernoulli p)) = atan(p)
arctan :: (MonadPrim m) => Buffon m Bool -> Buffon m Bool
arctan p = (do u <- createReal; evenParity (p*(p*(u*u)))) * p

-- | P(arcsin (bernoulli p)) = asin(p)/2
arcsin :: (MonadPrim m) => Buffon m Bool -> Buffon m Bool
arcsin p = mean (integrate (\w -> evenParity w * squareRoot (-w*w)) p) (-squareRoot (-p*p))

-- | P(erf (bernoulli p)) = sqrt(pi)erf(p)/2
erf :: (MonadPrim m) => Buffon m Bool -> Buffon m Bool
erf p = integrate (\w -> poisson' (w*w)) p

-- | P(pi8) = pi/8 (via (atan(1/2) + atan(1/3))/2)
pi8 :: (MonadPrim m) => Buffon m Bool
pi8 = mean (arctan toss) (arctan third)

-- | P(pi4) = pi/4 (via atan(1))
pi4 :: (MonadPrim m) => Buffon m Bool
pi4 = do u <- createReal; evenParity (u*u)

-- | P(zeta3) = 3zeta(3)/4
zeta3 :: (MonadPrim m) => Buffon m Bool
zeta3 = integrate' (\x -> integrate' (\y -> integrate' (\z -> evenParity (x*y*z)) 1) 1) 1
