module FragHeap where

import qualified Data.Vector as Vec
import qualified Data.Map as Map
import Misc
import Agent
import Node
import Injection

-- Fragmented Heap
type Address = Int
data FragHeap a = FragHeap { fresh :: Address
                           , elements :: Int
                           , array :: Vec.Vector (Maybe a)
                           , freeCells :: [Address]
                           }
  deriving (Show, Eq)


allocated :: FragHeap a -> Int
allocated = elements

dimension :: FragHeap a -> Int
dimension = Vec.length . array

flush :: FragHeap a -> FragHeap a
flush heap = heap{ fresh = 0, elements = 0, freeCells = [] }

fragmentation :: FragHeap a -> Int
fragmentation = length . freeCells

createHeap :: Int -> FragHeap a
createHeap n = FragHeap{ fresh = 0, elements = 0, array = Vec.replicate n Nothing, freeCells = [] }

free :: FragHeap a -> Address -> FragHeap a
free heap@(FragHeap{ elements = elems, freeCells = fcs }) addr = set heap' addr Nothing
  where heap' = heap{ elements = elems-1, freeCells = addr:fcs }

set :: FragHeap a -> Address -> Maybe a -> FragHeap a
set heap@(FragHeap{ array = array }) addr elt = heap{ array = updateVec array [(addr, elt)] "FragHeap.set" }

get :: FragHeap a -> Address -> Maybe a
get heap@(FragHeap{ array = array }) addr = join (array Vec.!? addr)

