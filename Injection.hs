module Injection( InjectionId, InjectionMap, codomain ) where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Agent (AgentId)
import Misc

-- Injection
type NodeId = Int
type NodeSet = Set.Set NodeId

type InjectionId = Int
type InjectionMap = Map.Map AgentId NodeId

-- Returns Just (injmap, codomain) where injmap is the joined injection of
-- the first and second argument and codomain is the set of visited nodes
-- Returns Nothing if there is a clash
codomain :: InjectionMap -> (InjectionMap, NodeSet) -> Maybe (InjectionMap, NodeSet)
codomain phi (inj, cod) = foldM (flip addEmbedding) (inj, cod) (Map.toList phi)
  where addEmbedding :: (AgentId, NodeId) -> (InjectionMap, NodeSet) -> Maybe (InjectionMap, NodeSet)
        addEmbedding (i, j) (map, set) = do guard $ Set.notMember j set -- make sure it's not a clash!
                                            return (Map.insert i j map, Set.insert j set)


