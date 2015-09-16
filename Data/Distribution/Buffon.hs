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
    poisson, poisson', logarithmic, logarithmic',
    squareRoot, ramanujan, arctan, integrate, createReal,
    pi8, pi4
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

-- uniform :: (MonadPrim m, Variate a) => Rand m a
-- Variate includes Bool, Double, Int, Word, (a,b), (a,b,c), (a,b,c,d)

----

-- | Toss a coin.  Calculates: P(toss) = 1/2
toss :: (MonadPrim m) => Buffon m Bool
toss = Buffon uniform

-- | A biased coin. Calculates: P(third) = 1/3
third :: (MonadPrim m) => Buffon m Bool
third = do
    a <- toss
    b <- toss
    if a && b then third else return (not (a||b))

toNumberWith :: (Fractional n, MonadPrim m) => Int -> Buffon m Bool -> m n
toNumberWith n p = runBuffon (go n 0)
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

--   Calculates: P(bernoulli x) = x
--  If P(p) = x then p = bernoulli x
-- bernoulli x = fmap (\n -> bits x !! (n+1) == 1) (geometric toss)
--  where bits x returns the bits of the binary expansion of x

-- Cheating bernoulli
bernoulli :: (Ord n, Variate n, Fractional n, MonadPrim m) => n -> Buffon m Bool
bernoulli p = do
    x <- Buffon uniform
    if x <= p then 1 else 0

-- | Calculates: P(if_ (bernoulli r) (bernoulli p) (bernoulli q)) = rp + (1-r)q
if_ :: (MonadPrim m) => Buffon m Bool -> Buffon m a -> Buffon m a -> Buffon m a
if_ r p q = do b <- r; if b then p else q

-- | Calculates: P(mean (bernoulli p) (bernoulli q)) = (p+q)/2
mean :: (MonadPrim m) => Buffon m a -> Buffon m a -> Buffon m a
mean p q = if_ toss p q

instance Eq (Buffon m a) where (==) = error "(==) not defined for Buffon"

instance Show (Buffon m a) where show _ = "<buffon>"

-- Note: These don't obey the laws you'd expect (like)
-- They are right-biased insofar as:
-- fix (\p -> p*q) == undefined (same for +)
-- but
-- fix (\q -> p+q) is at least as defined as p
instance (MonadPrim m) => Num (Buffon m Bool) where
    p * q = if_ p q 0            -- | Calculates: P(bernoulli p*bernoulli q) = pq
    p + q = if_ p 1 q            -- | Calculates: P(bernoulli p+bernoulli q) = p + q - pq
    negate p = not <$> p         -- | Calculates: P(-bernoulli p)  = 1 - p
    fromInteger 0 = return False -- | Calculates: P(0)   = 0
    fromInteger 1 = return True  -- | Calculates: P(1)   = 1
    abs = error "abs not defined for Buffon"
    signum = error "signum not defined for Buffon"

----

-- | Calculates: P(evenParity (bernoulli p)) = 1/(1+p)
evenParity :: (MonadPrim m) => Buffon m Bool -> Buffon m Bool
evenParity p = fix (\q -> if_ p (if_ p q 0) 1)

-- | Calculates: P(geometric (bernoulli p) == r) = (1-p)p^r
geometric :: (MonadPrim m) => Buffon m Bool -> Buffon m Int
geometric p = go 0
    where go !acc = if_ p (go (acc+1)) (return acc)

{-

von Neumann schema

Let Perms be a subset of the class of all permutations.
Let F_n be the number of permutations of n items in Perms.
Define F(z) = sum_(n>=0) F_n z^n/n!, i.e. the exponential generating function.
Let U = (U_1, ..., U_n) be a vector of bit streams.
Let type(U) be the permutation that sorts U.  type(U) is the order type of U.
The von Neumann schema is:

vN[Perms] p = go 0
    where go k = do
            n <- geometric p
            let U be an n-vector of uniformly distributed bit streams
            if type(U) in Perms then return (n, k) else go (k+1)

P(fst (vN[Perms] (bernoulli p)) == n) = F_n/F(p) p^n/n!
s = (1-p)F(p)
P(snd (vN[Perms] (bernoulli p)) == k) = s(1-s)^(k-1)
sum_(k>=1) k P(snd (vN[Perms] (bernoulli p)) == k) = 1/s

-}

-- | Calculates: P(fst (poisson (bernoulli p)) == r) = exp(-p)p^r/r!
-- | Fits the von Neumann schema with F(z) = exp(z)
-- Note: P(liftM2 (+) (fst (poisson (bernoulli p))) (fst (poisson (bernoulli q))) == r) = exp(-p-q)(p+q)^r/r!
poisson :: (MonadPrim m) => Buffon m Bool -> Buffon m (Int, Int)
poisson p = go 1
    where go !k = do
            n <- geometric p
            let loop 0  _ = return (n,k)
                loop 1  _ = return (n,k)
                loop i bs = walk bs []
                    where walk [] acc = walk' acc
                          walk (b:bs) acc = do
                            b' <- toss
                            case compare b b' of
                                LT -> go (k+1)
                                EQ -> walk bs (b:acc)
                                GT -> loop (i-1) acc
                          walk' acc = do
                            b <- toss
                            b' <- toss
                            case compare b b' of
                                LT -> go (k+1)
                                EQ -> walk' (b':acc)
                                GT -> loop (i-1) acc
            loop n []

-- | Calculates: P(poisson' (bernoulli p)) = exp(-p) = P(fst (poisson (bernoulli p)) == 0)
poisson' :: (MonadPrim m) => Buffon m Bool -> Buffon m Bool
poisson' = fmap ((0==) . fst) . poisson

-- | Calculates: P(fst (logarithmic (bernoulli p)) == r) = -p^r/(rlog(1-p))
-- | Fits the von Neumann schema with F(z) = -log(1-z)
logarithmic :: (MonadPrim m) => Buffon m Bool -> Buffon m (Int, Int)
logarithmic p = go 1
    where go !k = do
            n <- geometric p
            let loop 0 = go (k+1)
                loop 1 = return (n,k)
                loop i = do
                    b <- toss
                    let inner 0 !acc = loop acc
                        inner j acc = do
                            b' <- toss
                            case compare b b' of
                                LT -> go (k+1)
                                EQ -> inner (j-1) (acc+1)
                                GT -> inner (j-1) acc
                    inner (i-1) 1
            loop n

-- | Calculates: P(logarithmic' (bernoulli p)) = -p/log(1-p) = P(fst (logarithmic (bernoulli p)) == 1)
logarithmic' :: (MonadPrim m) => Buffon m Bool -> Buffon m Bool
logarithmic' = fmap ((1==) . fst) . logarithmic

-- | Calculates: P(squareRoot (bernoulli p)) = sqrt(1-p)
squareRoot :: (MonadPrim m) => Buffon m Bool -> Buffon m Bool
squareRoot p = go 0
    where go !c = if_ p (bump (bump go) c) (return (c==0))
          bump k !c = mean (k (c+1)) (k (c-1))

-- | Calculates: P(ramanujan) = 1/pi
ramanujan :: (MonadPrim m) => Buffon m Bool
ramanujan = do
    x1 <- geometric (toss*toss)
    x2 <- geometric (toss*toss)
    b <- bernoulli (5/9 :: Double)
    let t = 2*(if b then x1 + x2 + 1 else x1 + x2)
    let go 0 !c = return $ c == 0
        go i  c = mean (go (i-1) (c+1)) (go (i-1) (c-1))
    go t 0 * go t 0 * go t 0

-- Close enough to a real...
-- We could save random bits by flipping on demand and caching the results but it doesn't seem worth it...
createReal :: (MonadPrim m) => Buffon m (Buffon m Bool)
createReal = do
    u <- Buffon uniform
    return (do
        n <- geometric toss
        return (testBit (u :: Word64) n))

integrate :: (MonadPrim m) => (Buffon m Bool -> Buffon m Bool) -> Buffon m Bool -> Buffon m Bool
integrate f p = createReal >>= f . (p*)

-- | Calculates: P(arctan (bernoulli p)) = atan p
arctan :: (MonadPrim m) => Buffon m Bool -> Buffon m Bool
arctan p = p * (do u <- createReal; evenParity (p*(p*(u*u))))

-- | Calculates: P(pi8) = pi/8 (via (atan(1/2) + atan(1/3))/2)
pi8 :: (MonadPrim m) => Buffon m Bool
pi8 = mean (arctan toss) (arctan third)

-- | Calculates: P(pi4) = pi/4 (via atan(1))
pi4 :: (MonadPrim m) => Buffon m Bool
pi4 = do u <- createReal; evenParity (u*u)

-- | Calculates: P(zeta3) = 3zeta(3)/4
zeta3 :: (MonadPrim m) => Buffon m Bool
zeta3 = integrate (\x -> integrate (\y -> integrate (\z -> evenParity (x*y*z)) 1) 1) 1

{-
alternating :: (MonadPrim m) => Bool -> Buffon m Bool -> Buffon m (Int, Int)
alternating isEven p = go 1
    where go !k = do
            n <- geometric p
            let loop True 0  _ = return (n,k)
                loop True 1  _ = return (n,k)
                loop False 0 _ = go (k+1)
                loop False 1 _ = go (k+1)
                loop !p !i bs = walk (reverse bs) []
                    where walk [] acc = walk' acc
                          walk (b:bs) acc = do
                            b' <- toss
                            case if p then compare b b' else compare b' b of
                                LT -> go (k+1)
                                EQ -> walk bs (b:acc)
                                GT -> loop (not p) (i-1) acc
                          walk' acc = do
                            b <- toss
                            b' <- toss
                            case if p then compare b b' else compare b' b of
                                LT -> go (k+1)
                                EQ -> walk' (b':acc)
                                GT -> loop (not p) (i-1) acc
            loop isEven n []
-}
