{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}

-- From "On Buffon Machines and Numbers" by Flajolet, Pelletier, and Soria

module Data.Distribution.Buffon where
import Control.Monad.IO.Class ( MonadIO )
import Control.Monad.Primitive ( PrimMonad )
import Control.Monad.Primitive.Class ( MonadPrim(..) )
import Control.Monad.ST (ST, runST)
import Control.Monad.Trans.Class ( MonadTrans )
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

-- | Toss a coin.  Calculates: 0.5
toss :: (MonadPrim m) => Buffon m Bool
toss = Buffon uniform

toNumberWith :: (Fractional n, MonadPrim m) => Int -> Buffon m Bool -> m n
toNumberWith n p = runBuffon (go n 0)
    where go 0 !acc = return (acc/fromIntegral n)
          go c acc = if_ p (go (c-1) (acc+1)) (go (c-1) acc)

toNumberM :: (Fractional n, MonadPrim m) => Buffon m Bool -> m n
toNumberM = toNumberWith 1000000

-- | Estimate the probability of getting True
toNumber :: (Fractional n) => (forall s. Buffon (ST s) Bool) -> n
toNumber p = runST (toNumberM p)

----

-- | Calculates: rp + (1-r)q
if_ :: (MonadPrim m) => Buffon m Bool -> Buffon m a -> Buffon m a -> Buffon m a
if_ r p q = do b <- r; if b then p else q

-- | Calculates: (p+q)/2
mean :: (MonadPrim m) => Buffon m a -> Buffon m a -> Buffon m a
mean p q = if_ toss p q

instance Eq (Buffon m a)
instance Show (Buffon m a) where show _ = "<buffon>"

instance (MonadPrim m) => Num (Buffon m Bool) where
    p * q = if_ p q (return False) -- | Calculates: pq
    p + q = if_ p (return True) q  -- | Calculates: p + q - pq
    negate p = fmap not p          -- | Calculates: 1 - p
