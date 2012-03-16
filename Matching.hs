module Matching where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Agent as A
import qualified Node as N
import qualified Mixture as M
import qualified Injection as I
import qualified SiteGraph as SG
import Misc
import Control.Monad (foldM)

type Embedding = (A.AgentId, N.NodeId)
type EmbeddingSet = Set.Set Embedding

-- Returns (Just componentInjection) if mix anchored at agentRootId has an injection in sg at nodeRootId
-- defaults: checkAdditionalEdges = True; alreadyDone = Set.empty
component :: I.InjectionMap -> A.AgentId -> SG.SiteGraph -> A.AgentId -> M.Expr -> Bool -> EmbeddingSet ->
             Maybe (I.InjectionMap, N.PortMap)
component embedding agentRootId sg nodeRootId mix checkAdditionalEdges alreadyDone = 
  do (partialEmbedding, portMap) <- reco [(agentRootId, nodeRootId)] embedding Map.empty
     portMap' <- if checkAdditionalEdges -- checking edges not in the spanning tree only if unsure of the embedding
                   then return portMap
                   else foldM (flip . uncurry $ checkEdge partialEmbedding) portMap internalEdges
     return (partialEmbedding, portMap')

  where reco :: [Embedding] -> I.InjectionMap -> N.PortMap -> Maybe (I.InjectionMap, N.PortMap)
        reco [] partialEmbedding portMap = return (partialEmbedding, portMap)
        reco ((agentId, nodeId):queue) partialEmbedding portMap =
          -- Avoid adding twice the same embedding and make sure names match
          do guard $ Set.notMember (agentId, nodeId) alreadyDone && N.nameId node == A.nameId agent
             (queue', portList) <- foldM (flip $ uncurry addSite) (queue, []) (Map.toList $ A.interface agent)
             reco queue' (Map.insert agentId nodeId partialEmbedding) (Map.insert nodeId portList portMap)
          where node = SG.nodeOfId nodeId sg ? "Matching.component: node not found"
                agent = M.agentOfId agentId mix ? "Matching.component: agent not found"

                addSite :: A.SiteId -> A.Site -> ([Embedding], N.PortList) -> Maybe ([Embedding], N.PortList)
                addSite siteId (int, lnk) (queue, portList) = 
                  do portList' <- N.test (node, siteId) (int, lnk) portList
                     case M.followInSpanningTree agentRootId (agentId, siteId) mix of
                       Nothing -> return (queue, portList')
                       Just (agentId', siteId') ->
                         do (nodeId', siteId'') <- N.follow node siteId -- no need to add siteId'' in the portList see remark 29/06
                            guard $ siteId' == siteId''
                            return ((agentId', nodeId'):queue, portList')

        internalEdges = Map.toList $ M.internalEdges agentRootId mix

        checkEdge :: I.InjectionMap -> (A.AgentId, A.SiteId) -> (A.AgentId, A.SiteId) -> N.PortMap -> Maybe N.PortMap
        checkEdge partialEmbedding (ai, si) (aj, sj) portMap =
          do portList_i' <- N.test (node_i, si) (int_i, lnk_i) portList_i
             let portMap' = Map.insert ni portList_i' portMap
             (nx, sx) <- N.follow node_i si

             nj <- Map.lookup aj partialEmbedding
             node_j <- SG.nodeOfId nj sg
             agent_j <- M.agentOfId aj mix
             (int_j, lnk_j) <- Map.lookup sj (A.interface agent_j)

             N.test (node_j, sj) (int_j, lnk_j) [] -- no need to modify portMap'
             guard $ nj == nx && sj == sx
             return portMap'

          where ni = Map.lookup ai partialEmbedding ? "Matching.component: invariant violation"
                node_i = SG.nodeOfId ni sg ? "Matching.component: not a valid node address (" ++ show ni ++ ")"
                agent_i = M.agentOfId ai mix ? "Matching.component: agent " ++ show ai ++ " not found"
                (int_i, lnk_i) = Map.lookup si (A.interface agent_i) ? "Matching.component: site " ++ show si ++ " not found in agent " ++ show agent_i
                portList_i = Map.lookup ni portMap ? "Matching.component: node not found in portMap"


