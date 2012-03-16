module InjectionVector where

import qualified Data.Vector as Vec
import qualified Data.Map as Map
import System.Random (randomRIO)

import Injection
import Misc

type MaskId = Int
data InjVec = InjVec { newId :: InjectionId
                     , array :: Vec.Vector (Maybe InjectionMap) -- indexed by mask id
                     , elems :: Int
                     , mask :: Map.Map InjectionId MaskId
                     , unmask :: Map.Map MaskId InjectionId
                     }
  deriving (Show, Eq)

(!?) :: InjVec -> InjectionId -> Maybe InjectionMap
(InjVec{ array = array, mask = mask }) !? injId = join (array Vec.!? maskId)
  where maskId = Map.lookup injId mask ? "(InjectionVector.!?): injection id " ++ show injId ++ " not found"

size :: InjVec -> Int
size = elems

create :: Int -> InjVec
create size = InjVec { newId = 0
                     , array = Vec.replicate size Nothing
                     , elems = 0
                     , mask = Map.empty
                     , unmask = Map.empty
                     }

{-
foldHeap :: (InjectionId -> InjectionMap -> b -> b) -> b -> InjVec -> b
foldHeap f seed (InjVec{ array = array, unmask = unmask }) = Vec.ifoldr g seed array
  where g _ Nothing acc = acc
        g maskId (Just inj) acc = f injId inj acc
          where injId = Map.lookup maskId unmask ? "InjectionVector.foldHeap: mask id " ++ show maskId ++ " not found"
-}

defaultInjVecSize :: Int
defaultInjVecSize = 5

remove :: InjectionId -> InjVec -> InjVec
remove injId injVec@(InjVec{ array = array, newId = newId, elems = elems, mask = mask, unmask = unmask }) =
  injVec{ array = updateVec array [(maskId, Just lastVal), (lastMask, Nothing)] "InjectionVector.remove"
        , elems = elems - 1
        , mask   = Map.insert lastId maskId $ Map.delete injId mask
        , unmask = Map.insert maskId lastId $ Map.delete lastMask unmask
        }
  where maskId = Map.lookup injId mask ? "InjectionVector.remove: injection id " ++ show injId ++ " not found"
        lastMask = elems - 1
        lastId = Map.lookup lastMask unmask ? "InjectionVector.remove: mask id " ++ show lastMask ++ " not found"
        lastVal = join (array Vec.!? lastMask) ? "InjectionVector.remove: mask id " ++ show lastMask ++ " not found"

alloc :: InjectionMap -> InjVec -> (InjectionId, InjVec)
alloc inj injVec@(InjVec{ array = array, elems = elems, newId = newId, mask = mask, unmask = unmask }) =
  (newId, injVec{ array = updateVec array' [(elems, Just inj)] "InjectionVector.alloc"
                , elems = elems + 1
                , newId = newId + 1
                , mask = Map.insert newId elems mask
                , unmask = Map.insert elems newId unmask
                })
  where array' | elems == Vec.length array = array Vec.++ Vec.replicate (elems + 2) Nothing -- array is full -- why +2?
               | otherwise = array

random :: InjVec -> IO InjectionMap
random (InjVec{ array = array, elems = elems }) =
  do rnd <- randomRIO (0, elems-1)
     return (join (array Vec.!? rnd) ? "InjectionVector.random: mask id " ++ show rnd ++ " not found")


