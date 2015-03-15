{-- This module implements infinite arrays, that is, arrays that grow
    transparently upon demand. -}

module Language.Inferno.M.InfiniteArray where


-- import Data.Array.IO
-- import Data.IORef

import Language.Inferno.SolverM

import Data.Array.MArray
import Control.Monad.Ref
import Control.Monad

data InfiniteArray a = InfiniteArray {
  defa  :: a,
  table :: (Ref M) (RepArray Int a)
}

make :: Int -> a -> M (InfiniteArray a)
make default_size x = do
  t <- newArray (0, default_size) x
  r <- newRef t
  return $ InfiniteArray x r

get :: InfiniteArray b -> Int -> M b
get a i = do
  ensure a i
  t <- readRef (table a)
  readArray t i

set :: InfiniteArray e -> Int -> e -> M ()
set a i x = do
  ensure a i
  t <- readRef (table a)
  writeArray t i x

---------------------------------------------------

newLength length i =
  if i < length
  then length
  else newLength (2 * length) i

ensure a i = do
  t <- readRef (table a)
  (_,length) <- getBounds t
  when (i >= length) $ do
    t' <- newArray (0, newLength (2 * length) i) (defa a)
    forM_ [0 .. (length-1)] (\ i -> do
        x <- readArray t i
        writeArray t' i x)
    writeRef (table a) t'
  
      
  

