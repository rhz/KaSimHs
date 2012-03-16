module SiteGraph( SiteGraph, Radius, Depth, DistMap, createGraph, size, defaultGraphSize, dimension
                , foldl', ifoldl', nodeOfId, addNode, addNodes, removeNode, replaceNode, replaceNodes, neighborhood, addLift
                ) where

import Prelude hiding (any) --, foldr)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Vector as Vec
import Data.Foldable (any)
import Node
import FragHeap
import Injection
import Agent
import Misc

-- NodeId = Address 
type NodeHeap = FragHeap Node
type SiteGraph = NodeHeap
type Radius = Int
type Depth = Int
type DistMap = Map.Map Address Depth


size :: SiteGraph -> Int
size = allocated

defaultGraphSize :: Int
defaultGraphSize = 5

{-
foldr :: (Node -> a -> a) -> a -> SiteGraph -> a
foldr f acc sg = Vec.foldr g acc (array sg)
  where g Nothing acc = acc
        g (Just x) acc = f x acc
-}

ifoldl' :: (a -> NodeId -> Node -> a) -> a -> SiteGraph -> a
ifoldl' f acc sg = Vec.ifoldl' g acc (array sg)
  where g acc _ Nothing = acc
        g acc i (Just x) = f acc i x

createGraph :: Int -> SiteGraph
createGraph = createHeap

nodeOfId :: Address -> SiteGraph -> Maybe Node
nodeOfId = flip get


addNode :: SiteGraph -> Node -> (SiteGraph, NodeId)
addNode heap@(FragHeap{ elements = elems, fresh = freshAddr }) elt = aux $ freeCells heap
  where aux (addr:fcs) = (heap'{ freeCells = fcs, elements = elems+1 }, addr)
          where heap' = set heap addr (Just $ allocate elt addr)
        aux [] | freshAddr == dimension heap = addNode heap{ array = biggerArray } elt
               | otherwise = (heap'', freshAddr)
          where heap' = set heap freshAddr (Just $ allocate elt freshAddr)
                heap'' = heap'{ fresh = freshAddr+1, elements = elems+1 }

                biggerArray = array heap Vec.++ Vec.replicate (dimension heap + 2) Nothing -- why +2?

addNodes :: SiteGraph -> NodeMap -> SiteGraph
addNodes = Map.foldl' ((fst .) . addNode)

removeNode :: SiteGraph -> Address -> SiteGraph
removeNode = free

replaceNode :: SiteGraph -> NodeId -> Node -> SiteGraph
replaceNode sg nodeId node' = set sg nodeId (Just node')

replaceNodes :: SiteGraph -> [(NodeId, Node)] -> SiteGraph
replaceNodes = foldl' f
  where f sg = uncurry $ replaceNode sg

neighborhood :: SiteGraph -> Address -> Radius -> Set.Set Int -> DistMap
neighborhood sg id radius interruptWith = iter [id] (Map.singleton id 0)
  where iter :: [Address] -> DistMap -> DistMap
        iter [] distMap = distMap
        iter (addr:todo) distMap
            | radius >= 0 && depth+1 > radius = iter todo distMap
            | any (`Map.member` distMap') interruptWith = distMap'
            | otherwise =  iter todo' distMap'
          where depth = Map.lookup addr distMap ? "SiteGraph.neighborhood: invariant violation"
                (distMap', todo') = markNext addr (depth+1) distMap todo

        markNext :: Address -> Depth -> DistMap -> [Address] -> (DistMap, [Address])
        markNext addr depth distMap todo = foldStatus addLink (distMap, todo) node
          where node = nodeOfId addr sg ? "SiteGraph.neighborhood: node not found"
                addLink :: (DistMap, [Address]) -> SiteId -> PortStatus -> (DistMap, [Address])
                addLink (distMap, todo) _ (_, FPtr _ _)   = error "SiteGraph.neighborhood"
                addLink (distMap, todo) _ (_, Null)       = (distMap, todo)
                addLink (distMap, todo) _ (_, Ptr nbId _) = if visited
                                                              then (distMap', todo)
                                                              else (distMap', nbId:todo)
                  where (visited, distMap') = addMin nbId depth distMap

        addMin :: Address -> Depth -> DistMap -> (Bool, DistMap)
        addMin id depth distMap = if Map.member id distMap
                                    then (True, distMap)
                                    else (False, Map.insert id depth distMap)


addLift :: Lift -> PortMap -> SiteGraph -> SiteGraph
addLift lift portMap sg = Map.foldrWithKey addPortList sg portMap
  where addPortList :: AgentId -> PortList -> SiteGraph -> SiteGraph
        addPortList nodeId portList sg = set sg nodeId (Just $ addDeps node lift portList)
          where node = nodeOfId nodeId sg ? "SiteGraph.addLift: node not found"


