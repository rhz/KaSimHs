module Misc((?), fromMaybe, foldl', foldM, liftM, join, guard, infinity, updateVec) where

import qualified Data.Vector as Vec
import Control.Monad (foldM, liftM, join, guard)
import Data.Maybe (fromMaybe)
import Data.List (foldl')

infinity :: (Fractional a) => a
infinity = 1/0

-- Fns for better error reporting
infixr 1 ?
(?) :: Maybe a -> String -> a
x ? s = fromMaybe (error s) x

updateVec :: Vec.Vector a -> [(Int, a)] -> String -> Vec.Vector a
updateVec vec vals fnName = if all (< len) indices
                              then Vec.unsafeUpd vec vals
                              else error $ fnName ++ ": index/indices out of bounds (" ++ show (filter (>= len) indices) ++ ", " ++ show len ++ ")"
  where len = Vec.length vec
        indices = map fst vals

-- Monadic catMaybes
--joinMaybes :: MonadPlus m => m (Maybe a) -> m a
--joinMaybes = (>>= maybe mzero return)

