module Mixture where

import Prelude hiding (span, null)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Vector as Vec
import Agent
import Misc

-- Expressions
data Link = Link AgentId SiteId | Closed
  deriving (Show, Eq)
type EdgeId = Int
type PairingMap = Map.Map EdgeId Link
type NewEdgesMap = Map.Map (AgentId, SiteId) (AgentId, SiteId)
data Context = Context { pairing :: PairingMap
                       , currId :: AgentId
                       , newEdges :: NewEdgesMap
                       }
  deriving (Show, Eq)

type IdPair = (AgentId, SiteId)
type Span = Map.Map IdPair IdPair
type InternalEdges = Map.Map IdPair IdPair
-- TODO what's a Covering?
data Covering = Covering { span_ :: Span
                         , internal_ :: InternalEdges
                         }
  deriving (Show, Eq)

type CoveringMap = Map.Map AgentId Covering

-- TODO is this used for unary vs binary kinetic rates?
data Constraints = PreviouslyDisconnected AgentId AgentId | PreviouslyConnected AgentId AgentId
  deriving (Show, Eq)

type MixtureId = Int
type ComponentId = Int

type AgentIdSet = Set.Set AgentId
type AgentIdVec = Vec.Vector AgentId
type ComponentVec = Vec.Vector ComponentId
type IntVec = Vec.Vector Int

type Graph = Map.Map IdPair IdPair
type Name2Ids = Map.Map (AgentNameId, ComponentId) AgentIdSet

data Expr = Expr { agents :: Map.Map AgentId Agent
                 , siteNumber :: Int
                 , graph :: Graph
                 , enumCov :: Maybe CoveringMap
                 , constraints {-rejectUponMatching-} :: Map.Map Int Constraints -- what's this for?
                 , idsOfNames :: Name2Ids
                 , arity :: Maybe Int
                 , getId {-mixId-} :: Maybe MixtureId
                 , ccOfId :: Maybe ComponentVec --  AgentId -> ComponentId
                 , sizeOfCc :: IntVec     -- ComponentId -> size
                 , rootOfCc :: AgentIdVec -- ComponentId -> AgentId
                 }
  deriving (Show, Eq)


emptyExpr :: Maybe MixtureId -> Expr
emptyExpr id = Expr{ agents = Map.empty
                   , siteNumber = 0
                   , graph = Map.empty
                   , enumCov = Nothing
                   , constraints {-rejectUponMatching-} = Map.empty
                   , idsOfNames = Map.empty
                   , arity = Nothing
                   , getId {-mixId-} = id
                   , ccOfId = Nothing
                   , sizeOfCc = Vec.empty
                   , rootOfCc = Vec.empty
                   }

null :: Expr -> Bool
null = Map.null . agents

span :: AgentId -> Expr -> Span
span root (Expr {enumCov = ec}) = fromMaybe Map.empty (liftM span_ $ Map.lookup root hsh)
  where hsh = ec ? "Mixture.span: covering not computed"

internalEdges :: AgentId -> Expr -> InternalEdges
internalEdges root (Expr {enumCov = ec}) = fromMaybe Map.empty (liftM internal_ $ Map.lookup root hsh)
  where hsh = ec ? "Mixture.internalEdges: covering not computed"

componentOfId :: AgentId -> Expr -> Maybe ComponentId
componentOfId agentId mix = vec Vec.!? agentId
  where vec = ccOfId mix ? "Mixture.componentOfId: ccOfId not computed"

setRootOfCc :: Expr -> Expr
setRootOfCc mix = mix{ rootOfCc = Vec.fromList [max a (-1) | a <- cId] }
  where cId = Vec.toList $ ccOfId mix ? "Mixture.setRootOfCc: ccOfId not computed"
        len = arity mix ? "Mixture.setRootOfCc: arity not computed"

agentOfId :: AgentId -> Expr -> Maybe Agent
agentOfId id (Expr {agents = as}) = Map.lookup id as

idsOfName :: (AgentId, ComponentId) -> Expr -> AgentIdSet
idsOfName k (Expr {idsOfNames = ids}) = fromMaybe Set.empty (Map.lookup k ids)

isBound :: (AgentId, SiteId) -> Expr -> Bool
isBound (agentId, siteId) mix = isBnd lnk
  where (Agent _ intf) = agentOfId agentId mix ? "Mixture.isBound: agent '" ++ show agentId ++ "' does not exist"
        (_, lnk) = Map.lookup siteId intf ? "Mixture.isBound: no site '" ++ show siteId ++ "' in agent '" ++ show agentId ++ "'"

        isBnd Bound = True
        isBnd _ = False

compose :: AgentId -> Agent -> Expr -> NewEdgesMap -> Expr
compose id agent mix@(Expr {agents = as, siteNumber = siteNum, graph = g}) newEdges =
  mix{ graph = g', siteNumber = siteNum', agents = Map.insert id agent as }
  where (g', siteNum') = Map.foldrWithKey addEdge (g, siteNum) newEdges
        addEdge :: (AgentId, SiteId) -> (AgentId, SiteId) -> (Graph, Int) -> (Graph, Int)
        addEdge (a, i) (b, j) (g, siteNum)
          | id /= a = error $ "Mixture.compose: invariant violation 1 (" ++ show id ++ " /= " ++ show a ++ ", " ++ show b ++ ")"
          | a < b   = error $ "Mixture.compose: invariant violation 2 (" ++ show a ++ " < " ++ show b ++ ")" -- spanning edge a -> b
          | otherwise = (Map.insert (b, j) (a, i) (Map.insert (a, i) (b, j) g), siteNum + 2)


followInSpanningTree :: AgentId -> (AgentId, SiteId) -> Expr -> Maybe (AgentId, SiteId)
followInSpanningTree rootId (agentId, siteId) mix = Map.lookup (agentId, siteId) sp
  where sp = span rootId mix -- spanning tree from root

-- Returns the agent id and site id of the neighbour if there's any
follow :: (AgentId, SiteId) -> Expr -> Maybe (AgentId, SiteId)
follow (agentId, siteId) (Expr {graph = graph}) = Map.lookup (agentId, siteId) graph


createSpanningTree :: AgentId -> Expr -> (Covering, AgentId) -- AgentId in the returned value is the smallest agent id belonging to the component
createSpanningTree agentId mix = depthFirst [agentId] (Set.singleton agentId) Map.empty Map.empty agentId
  where depthFirst :: [AgentId] -> AgentIdSet -> Span -> InternalEdges -> AgentId -> (Covering, AgentId)
        depthFirst [] _ m2Span m2Internal minId = (Covering{ span_ = m2Span, internal_ = m2Internal }, minId)
        depthFirst (aId:queue) viewed m2Span m2Internal minId =
          depthFirst queue' viewed' m2Span' m2Internal' (min aId minId)
          where
            (Agent _ intf) = agentOfId aId mix ? "Mixture.createSpanningTree: agent id " ++ show aId ++ " not found in mixture"
            (queue', viewed', m2Span', m2Internal') = foldr followSite (queue, viewed, m2Span, m2Internal) (Map.keys intf)

            followSite sId (queue, viewed, m2Span, m2Internal) = addAgent $ follow (aId, sId) mix
              where addAgent (Just (b, j)) 
                      | Set.notMember b viewed = (b:queue,
                                                  Set.insert b viewed, -- b added to queue and viewed
                                                  Map.insert (aId, sId) (b, j) m2Span,
                                                  m2Internal)
                      | (aId, sId) < (b, j) = (queue, viewed, m2Span, Map.insert (aId, sId) (b, j) m2Internal)
                      | otherwise = (queue, viewed, m2Span, m2Internal) -- unmodified
                    addAgent Nothing = (queue, viewed, m2Span, m2Internal) -- unmodified

type Ag2Cc = Map.Map AgentId ComponentId

enumAlternateAnchors :: Expr -> Expr
enumAlternateAnchors mix@(Expr {agents = as}) = mix{ enumCov = Just cov
                                                   , ccOfId = Just compOfId
                                                   , arity = Just compNum
                                                   , idsOfNames = ids
                                                   , sizeOfCc = sizeOfCc
                                                   }
  where numAgents = Map.size as
        (cov, compOfId, compNum, _) = Map.foldrWithKey addAgent (Map.empty, Vec.replicate numAgents (-1), 0, Map.empty) as

        addAgent :: AgentId -> Agent -> (CoveringMap, ComponentVec, ComponentId, Ag2Cc) -> (CoveringMap, ComponentVec, ComponentId, Ag2Cc)
        addAgent agentId agent (cov, compOfId, freshCcId, min2cc) = (cov', compOfId Vec.// [(agentId, ccId)], freshCcId', min2cc')
          where cov' = Map.insert agentId span cov
                (ccId, freshCcId', min2cc') = case Map.lookup minId min2cc of
                                                -- If minId is not yet registered in min2cc, then we create a new id and register it
                                                Nothing -> (freshCcId, freshCcId + 1, Map.insert minId freshCcId min2cc)
                                                Just ccId -> (ccId, freshCcId, min2cc)
                (span, minId) = createSpanningTree agentId mix -- minId: smallest agent id belonging to the component of agentId

        (ids, sizeOfCc) = Vec.ifoldr addComponent (Map.empty, Vec.replicate compNum 0) compOfId

        addComponent :: AgentId -> ComponentId -> (Name2Ids, IntVec) -> (Name2Ids, IntVec)
        addComponent agentId ccId (ids, sizeOfCc) = (ids', sizeOfCc')
          where ids' = Map.insert (agentNameId, ccId) (Set.insert agentId agentIdSet) ids
                sizeOfCc' = sizeOfCc Vec.// [(ccId, (size+1))]
                size = sizeOfCc Vec.! ccId

                (Agent agentNameId _) = agentOfId agentId mix ? "Mixture.enumAlternateAnchors: agent id " ++ show agentId ++ " not found"
                agentIdSet = fromMaybe Set.empty (Map.lookup (agentNameId, ccId) ids)

siteDefined :: SiteId -> Agent -> Maybe Site
siteDefined siteId agent = do (intState, lnkState) <- Map.lookup siteId (interface agent)
                              case intState of
                                Just _ -> Just (intState, lnkState)
                                Nothing -> case lnkState of
                                             Unspecified -> Nothing
                                             _ -> Just (intState, lnkState)

-- toKappa :: Bool -> Expr -> Env -> String

