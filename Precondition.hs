module Precondition where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Agent as A
import qualified Mixture as M
import qualified Node as N
import Dynamics (MatchingSet)
import Misc

data View = Free
          | Bnd1 N.NodeId A.SiteId
          | Bnd0
          | Int A.InternalStateId
  deriving (Show, Eq, Ord)

type Preconditions = Map.Map (N.NodeId, N.PortId, View) MatchingSet

empty :: Preconditions
empty = Map.empty

insert :: M.Expr -> Preconditions -> Preconditions
insert mix wuMap = Map.foldrWithKey addAgent wuMap (M.agents mix)
  where mixId = M.getId mix ? "Precondition.insert: missing id"
  
        addAgent :: A.AgentId -> A.Agent -> Preconditions -> Preconditions
        addAgent agentId agent wuMap = A.foldInterface addSite wuMap agent
          where agentName = A.nameId agent

                addSite :: A.SiteId -> A.Site -> Preconditions -> Preconditions
                addSite siteId (int, lnk) = addInt int . addLnk lnk
                  where ccId = M.componentOfId agentId mix ? "Precondition.insert: missing component"

                        addInt Nothing = id
                        addInt (Just int) = addCcToView (Int int)

                        addLnk A.Unspecified = id
                        addLnk A.Free = addCcToView Free
                        addLnk A.SemiLink = addCcToView Bnd0
                        addLnk A.Bound = addCcToView (Bnd1 nbName nbSiteId)
                          where nbName = A.nameId (M.agentOfId nbId mix ? "Precondition.insert: agent not found")
                                (nbId, nbSiteId) = M.follow (agentId, siteId) mix ? "Precondition.insert: neighbour not found"

                        addCcToView :: View -> Preconditions -> Preconditions
                        addCcToView view wuMap = Map.insert (agentName, siteId, view) (Set.insert (mixId, ccId) set) wuMap
                          where set = Map.findWithDefault Set.empty (agentName, siteId, view) wuMap


findAll :: N.NodeId -> N.PortId -> Maybe A.InternalStateId -> Maybe (N.NodeId, N.PortId) -> Bool -> Preconditions -> MatchingSet
findAll name siteId int lnk isFree wuMap = intSet int `Set.union` lnkSet lnk
  where intSet Nothing = Set.empty
        intSet (Just u) = Map.findWithDefault Set.empty (name, siteId, Int u) wuMap

        lnkSet Nothing | isFree = Set.empty
                       | otherwise = Map.findWithDefault Set.empty (name, siteId, Free) wuMap
        lnkSet (Just (name', siteId')) = Map.findWithDefault Set.empty (name, siteId, Bnd0) wuMap
                                         `Set.union`
                                         Map.findWithDefault Set.empty (name, siteId, Bnd1 name' siteId') wuMap

