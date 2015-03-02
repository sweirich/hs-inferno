{-- This module implements infinite arrays, that is, arrays that grow
    transparently upon demand. -}

module Language.Inferno.InfiniteArray where


-- import Data.Array.IO
-- import Data.IORef

import Data.Array.MArray
import Control.Monad.Ref
import Control.Monad

data InfiniteArray m ra a = InfiniteArray {
  def   :: a,
  table :: (Ref m) (ra Int a)
}

make :: (MonadRef m, MArray ra a m) => Int -> a -> m (InfiniteArray m ra a)
make default_size x = do
  t <- newArray (0, default_size) x
  r <- newRef t
  return $ InfiniteArray x r

get :: (MonadRef m, MArray a b m) => InfiniteArray m a b -> Int -> m b
get a i = do
  ensure a i
  t <- readRef (table a)
  readArray t i

set :: (MonadRef m, MArray a e m) => InfiniteArray m a e -> Int -> e -> m ()
set a i x = do
  ensure a i
  t <- readRef (table a)
  writeArray t i x

---------------------------------------------------

new_length length i =
  if i < length
  then length
  else new_length (2 * length) i

ensure a i = do
  t <- readRef (table a)
  (_,length) <- getBounds t
  when (i >= length) $ do
    t' <- newArray (0, new_length (2 * length) i) (def a)
    forM_ [0 .. (length-1)] (\ i -> do
        x <- readArray t i
        writeArray t' i x)
    writeRef (table a) t'
  
      
  

