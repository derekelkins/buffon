module Buffon where
import System.Random.MWC.Monad

newtype BuffonM m a = Buffon { unBuffon :: Rand m a }

runBuffon :: MonadPrim m => Buffon m a -> m a
runBuffon = runWithCreate . unBuffon

--runBuffonWithSystemRandomT :: (MonadPrim m, BasePrimMonad m ~ IO) => Buffon m a -> m a
runBuffonWithSystemRandomT = runWithSystemRandomT . unBuffon


