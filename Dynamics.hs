module Dynamics where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe (isJust, fromJust)
import Data.Foldable (foldlM)

import Agent
import qualified Mixture as M
import qualified Node as N
import Signature
import Env
import Misc

data Id = Fresh AgentId | Kept AgentId -- binding or modifying a port that has been added or kept from the lhs
  deriving (Show, Eq, Ord)

type Port = (Id, SiteId)
data Action = Bnd Port Port
            | Brk Port Bool -- Brk p b with b = True if Brk is side-effect free -- break link
            | Mod Port InternalStateId
            | Del N.NodeId
            | Add AgentId AgentNameId -- (id in mixture, agentId)
  deriving (Show, Eq)

type Balance = (Int, Int, Int) -- (#deleted, #preserved, #removed)

type ModifiedSiteSet = Set.Set N.ModifiedSite
type ModifiedSiteMap = Map.Map Id ModifiedSiteSet

data Rule = Rule{ k :: Double, -- AE -- standard kinetic constant
                  -- kUnary :: Maybe Double, -- Maybe AE -- possible unary kinetic rate -- what's this?
                  oversampling :: Maybe Double, -- boosted kinetic rate for Bologna technique
                  lhs :: M.Expr,
                  rhs :: M.Expr,
                  ruleId :: RuleId,
                  script :: [Action],
                  balance :: Balance,
                  added :: M.AgentIdSet,
                  sideEffects :: Bool,
                  modifiedSites :: ModifiedSiteMap }
  deriving (Show, Eq)

-- Simply put, Glueings and Matchings are between two Exprs (normally lhs -> rhs) and
-- InjectionMaps and Embeddings are between a Expr and a SiteGraph (eg lhs -> mixture)
type Glueing = Map.Map AgentId AgentId
type Matching = (AgentId, AgentId)
type MatchingSet = Set.Set Matching


-- Analyze the differences between the left-hand side and right-hand side of a rule
diff :: M.Expr -> M.Expr -> Env -> ([Action], Balance, M.AgentIdSet, ModifiedSiteMap, Bool)
diff m1 m2 env =
  (insts', balance, Set.fromList added, modifiedSites', sideEffects')
  where
    (prefix, deleted, added) = pairExprs m1 m2
    balance = (length deleted, length prefix, length added)
    deleteInst = map Del deleted -- insts are instructions
    createInst = map add added
    add id = Add id (nameId $ M.agentOfId id m2 ? "Dynamics.diff: agent not found in rhs")
    sideEffects = not $ null deleteInst
    (insts, modifiedSites) = foldr addConnections (deleteInst ++ createInst, Map.empty) added
    (insts', modifiedSites', sideEffects') = foldr addModifications (insts, modifiedSites, sideEffects) prefix

    addMap :: Id -> N.ModifiedSite -> ModifiedSiteMap -> ModifiedSiteMap
    addMap id siteType map = Map.insert id (Set.insert siteType set) map
      where set = Map.findWithDefault Set.empty id map

    -- Adding connections of new agents if partner has a lower id
    addConnections :: AgentId -> ([Action], ModifiedSiteMap) -> ([Action], ModifiedSiteMap)
    addConnections id (insts, modifiedSites) = (insts', modifiedSites')
      where (Agent nameId intf) = M.agentOfId id m2 ? "Dynamics.diff: agent not found in rhs"
            sign@(Sig _ (_, siteMap) _) = getSig nameId env ? "Dynamics.diff: signature not found"

            modifiedSites' = foldr addSite modifiedSites (Map.elems siteMap)
            addSite :: SiteId -> ModifiedSiteMap -> ModifiedSiteMap
            addSite siteId idMap = addMap (Fresh id) (siteId, N.Int) (addMap (Fresh id) (siteId, N.Lnk) idMap)

            insts' = Map.foldrWithKey addInst insts intf
            msg = "Dynamics.diff: adding an agent that is not "

            defaultState :: SiteId -> Maybe InternalState
            defaultState siteId = internalStateOfNum siteId 0 sign

            addModInst :: Maybe InternalStateId -> Maybe InternalState -> SiteId -> [Action] -> [Action]
            addModInst Nothing  Nothing _ insts = insts
            addModInst (Just _) Nothing _ insts = insts -- DCDW: default will be assumed
            addModInst (Just stateId) (Just _) siteId insts = Mod (Fresh id, siteId) stateId : insts
            addModInst Nothing (Just _) _ _ = error $ msg ++ "supposed to have an internal state"

            addInst :: SiteId -> (Maybe InternalStateId, BindingState) -> [Action] -> [Action]
            addInst _ (_, Unspecified) _ = error $ msg ++ "fully described (unspecified binding state)"
            addInst siteId (internalStateId, Free)  insts = addModInst internalStateId (defaultState siteId) siteId insts
            addInst siteId (internalStateId, Bound) insts = if i < id || i == id && x < siteId
                                                              then Bnd (bndi, x) (Fresh id, siteId) : insts'
                                                              else insts'
              where insts' = addModInst internalStateId (defaultState siteId) siteId insts
                    (i, x) = M.follow (id, siteId) m1 ? msg ++ "fully described (semi link)"
                    bndi = if i `elem` added
                             then Fresh i
                             else Kept i

    -- Adding link and internal state modifications for agents conserved by the rule
    addModifications :: AgentId -> ([Action], ModifiedSiteMap, Bool) -> ([Action], ModifiedSiteMap, Bool)
    addModifications id (insts, modifiedSites, sideEffects) =
      Map.foldrWithKey addSite (insts, modifiedSites, sideEffects) intf1
      where
        (Agent _ intf1) = M.agentOfId id m1 ? "Dynamics.diff: agent not found in lhs"
        (Agent _ intf2) = M.agentOfId id m2 ? "Dynamics.diff: agent not found in rhs"

        addSite :: SiteId -> (Maybe InternalStateId, BindingState) -> ([Action], ModifiedSiteMap, Bool) -> ([Action], ModifiedSiteMap, Bool)
        addSite siteId (intStateId1, lnkState1) (insts, modifiedSites, sideEffects) =
          addLnkStates lnkState1 lnkState2 (insts', modifiedSites', sideEffects)
          where
            (insts', modifiedSites') = addIntStates intStateId1 intStateId2 (insts, modifiedSites)
            (intStateId2, lnkState2) = Map.lookup siteId intf2 ? "Dynamics.diff: invariant violation"

            addIntStates :: Maybe InternalStateId -> Maybe InternalStateId -> ([Action], ModifiedSiteMap) -> ([Action], ModifiedSiteMap)
            addIntStates (Just i) (Just j) (insts, idmap) =
              if i == j
                then (insts, idmap)
                else (insts', idmap')
              where insts' = Mod (Kept id, siteId) j : insts
                    idmap' = addMap (Kept id) (siteId, N.Int) idmap
            addIntStates (Just i) Nothing (insts, idmap) =
              error "Dynamics.diff: agent not instanciated on the right"
            addIntStates Nothing (Just j) (insts, idmap) = (insts', idmap')
              where insts' = Mod (Kept id, siteId) j : insts
                    idmap' = addMap (Kept id) (siteId, N.Int) idmap
            addIntStates Nothing Nothing (insts, idmap) = (insts, idmap)

            addLnkStates :: BindingState -> BindingState -> ([Action], ModifiedSiteMap, Bool) -> ([Action], ModifiedSiteMap, Bool)
            addLnkStates Bound Free (insts, idmap, sideEffects) = -- connected -> disconnected
              case M.follow (id, siteId) m1 of
                Just (id', siteId') -> -- generating a Brk instruction only for the smallest port
                  let kept = id' `elem` prefix
                      idmap' = if kept
                                 then addMap (Kept id) (siteId, N.Lnk) (addMap (Kept id') (siteId', N.Lnk) idmap)
                                 else addMap (Kept id) (siteId, N.Lnk) idmap
                      insts' = if id' < id || (id' == id && siteId' < siteId)
                                 then Brk (Kept id, siteId) True : insts
                                 else insts
                  in (insts', idmap', sideEffects)
                Nothing -> -- breaking a semi link so generate a Brk instruction
                  let idmap' = addMap (Kept id) (siteId, N.Lnk) idmap
                      insts' = Brk (Kept id, siteId) False : insts
                  in (insts', idmap', True)

            addLnkStates Bound Bound (insts, idmap, sideEffects) = -- connected -> connected
              case (M.follow (id, siteId) m1, M.follow (id, siteId) m2) of
                (Nothing, Just (id2, i2)) -> -- sub-case: semi-link -> connected
                  if id2 < id || (id2 == id && i2 < siteId)
                    then let insts' = Bnd (Kept id, siteId) (Kept id2, i2) : insts
                             idmap' = addMap (Kept id) (siteId, N.Lnk) (addMap (Kept id2) (i2, N.Lnk) idmap)
                         in (insts', idmap', True)
                    else (insts, idmap, sideEffects)
                (Just (id1, i1), Just (id2, i2)) -> -- sub-case: connected -> connected
                  if id2 < id || (id2 == id && i2 < siteId)
                    then let insts' = Bnd (Kept id, siteId) (Kept id2, i2) : insts
                             idmap' = if id1 `elem` prefix
                                        then addMap (Kept id1) (i1, N.Lnk) idmap
                                        else idmap
                             idmap'' = addMap (Kept id2) (i2, N.Lnk) idmap'
                             idmap''' = addMap (Kept id) (siteId, N.Lnk) idmap''
                         in (insts', idmap''', sideEffects)
                    else (insts, idmap, sideEffects)
                (Just (id1, i1), Nothing) -> -- sub-case: connected -> semi-link
                  error "Dynamics.diff: rhs has partial link state"
                (Nothing, Nothing) -> (insts, idmap, sideEffects) -- sub-case: semi-link -> semi-link

            addLnkStates Free Bound (insts, idmap, sideEffects) = -- free -> connected
              case M.follow (id, siteId) m2 of
                Nothing -> error "Dynamics.diff: rhs creates a semi-link" -- sub-case: free -> semi-link
                Just (id', siteId') -> -- sub-case: free -> connected
                  if (id' < id) || (id' == id && siteId' < siteId)
                    then let insts' = Bnd (Kept id, siteId) (Kept id', siteId') : insts
                             idmap' = addMap (Kept id) (siteId, N.Lnk) (addMap (Kept id') (siteId', N.Lnk) idmap)
                         in (insts', idmap', sideEffects)
                    else (insts, idmap, sideEffects)

            addLnkStates Free        Free        (insts, idmap, sideEffects) = (insts, idmap, sideEffects) -- free -> free
            addLnkStates SemiLink    SemiLink    (insts, idmap, sideEffects) = (insts, idmap, sideEffects) -- semilink -> semilink
            addLnkStates Unspecified Unspecified (insts, idmap, sideEffects) = (insts, idmap, sideEffects) -- wildcard -> wildcard

            addLnkStates Unspecified Free (insts, idmap, sideEffects) = (insts', idmap', True) -- wildcard -> free
              where insts' = Brk (Kept id, siteId) False : insts
                    idmap' = addMap (Kept id) (siteId, N.Lnk) idmap

            addLnkStates Unspecified Bound (insts, idmap, sideEffects) = -- wildcard -> connected
              case M.follow (id, siteId) m2 of
                Nothing -> error "Dynamics.diff: rhs turns a wildcard into a semi link"
                Just (id', siteId') -> if (id' < id) || (id' == id && siteId' < siteId)
                                         then let insts' = Bnd (Kept id, siteId) (Kept id', siteId') : insts
                                                  idmap' = addMap (Kept id) (siteId, N.Lnk)
                                                             (addMap (Kept id') (siteId', N.Lnk) idmap)
                                              in (insts', idmap', True)
                                         else (insts, idmap, sideEffects)

            addLnkStates lnk1 lnk2 _ = error $ "Dynamics.diff: rhs creates a wildcard (" ++ show lnk1 ++ " -> " ++ show lnk2 ++ ")" -- connected or free -> wildcard


-- Find the largest common prefix between the lhs and rhs.
-- Find also the agents that are created and deleted by the rule.
pairExprs :: M.Expr -> M.Expr -> ([AgentId], [AgentId], [AgentId])
pairExprs (M.Expr {M.agents = as1}) (M.Expr {M.agents = as2}) = (prefix, deleted, added)
  where
    (prefix, deleted, addIndex) = Map.foldrWithKey addAgent ([], [], Map.size as1) as1
    added = foldr (\id added -> if id < addIndex then added else id:added) [] (Map.keys as2)

    addAgent id a1 (prefix, [], addIndex) = case Map.lookup id as2 of
                                              Just a2 -> if idPreserving a1 a2
                                                           then (id:prefix, [], addIndex)
                                                           else (prefix, [id], min id addIndex)
                                              Nothing -> (prefix, [id], addIndex)
    addAgent id _ (prefix, deleted, addIndex) = (prefix, id:deleted, addIndex)

    -- Check whether a2 can be the residual of a1 for (same name, same sites)
    idPreserving :: Agent -> Agent -> Bool
    idPreserving (Agent id1 intf1) (Agent id2 intf2) =
      id1 == id2 && Set.null (Map.keysSet intf1 Set.\\ Map.keysSet intf2) -- `Set.union` (siteNames2 Set.\\ siteNames1))?


superpose :: [Matching] -> M.Expr -> M.Expr -> M.AgentIdSet -> Env -> Maybe Glueing
superpose todo lhs rhs added env = superpose' Map.empty Set.empty todo
  where superpose' :: Glueing -> MatchingSet -> [Matching] -> Maybe Glueing
        superpose' m alreadyDone [] = Just m
        superpose' m alreadyDone ((lhsId, rhsId):todo) =
          do guard $ nameLhs == nameRhs
             (todo', alreadyDone') <- foldM addSite (todo, alreadyDone) (Map.toList intfLhs)
             superpose' (Map.insert lhsId rhsId m) alreadyDone' todo'
          where lhsAgent@(Agent nameLhs intfLhs) = M.agentOfId lhsId lhs ? "Dynamics.superpose: agent id " ++ show lhsId ++ " not found in lhs (" ++ show lhs ++ ", " ++ show rhs ++ ")\n" ++ show env
                rhsAgent@(Agent nameRhs _) = M.agentOfId rhsId rhs ? "Dynamics.superpose: agent id " ++ show rhsId ++ " not found in rhs"

                addSite :: ([Matching], MatchingSet) -> (SiteId, Site) -> Maybe ([Matching], MatchingSet)
                addSite (todo, alreadyDone) (siteId, (int, lnk)) =
                  case M.siteDefined siteId rhsAgent of
                    Nothing -> Just (todo, alreadyDone) -- siteId is not in the agent in the rhs
                    Just (int', lnk') -> case (int, int') of
                                           (Just i, Just i') -> do guard $ i == i'
                                                                   checkBindingState lnk lnk'
                                           _ -> checkBindingState lnk lnk'
                  where
                    checkBindingState Bound Bound = checkNbs lhsNb rhsNb -- nb = neighbour
                      where lhsNb = M.follow (lhsId, siteId) lhs
                            rhsNb = M.follow (rhsId, siteId) rhs

                            checkNbs (Just (lhsId', siteId')) (Just (rhsId', siteId''))
                              | siteId' /= siteId'' = Nothing
                              | Set.member (lhsId', rhsId') alreadyDone = Just (todo, alreadyDone)
                              | otherwise = Just ((lhsId', rhsId') : todo, Set.insert (lhsId', rhsId') alreadyDone)
                            checkNbs _ _ = Just (todo, alreadyDone)

                    checkBindingState Free Free = Just (todo, alreadyDone)
                    checkBindingState Unspecified Unspecified = Just (todo, alreadyDone)
                    checkBindingState _ _ = Nothing


enable :: Rule -> M.Expr -> Env -> [Glueing]
enable (Rule{ modifiedSites = idmap, rhs = rhs, added = added }) lhs env =
  fst $ Map.foldrWithKey (unify . extractId) ([], Set.empty) idmap
  where
    extractId (Fresh agentId) = agentId -- id of the agent to which a modified site belongs
    extractId (Kept  agentId) = agentId

    -- agentId1 is the agent id of a site which is modified by the rule
    -- It'll be used as an anchor agent to try to glue the rhs of the rule with lhs
    unify :: AgentId -> ModifiedSiteSet -> ([Glueing], MatchingSet) -> ([Glueing], MatchingSet)
    unify agentId1 modifiedSites (glueings, alreadyDone) =
      Set.fold addGlueings (glueings, alreadyDone) candidates
      where candidates = foldr addCandidates Set.empty ccIds -- agent ids in lhs that have the name as agentId1
            nameId1 = nameId (M.agentOfId agentId1 rhs ? "Dynamics.enable: agent " ++ show agentId1 ++ " not found in rhs")

            ccIds = [0..arityLhs - 1]
            arityLhs = M.arity lhs ? "Dynamics.enable: arity of lhs has not been computed"

            addCandidates :: M.ComponentId -> M.AgentIdSet -> M.AgentIdSet
            addCandidates ccId = Set.union (M.idsOfName (nameId1, ccId) lhs)

            -- agentId2 is the agent id of a agent in lhs with the same name as agentId1
            -- Thus, it's a possible candidate for a glueing
            addGlueings :: AgentId -> ([Glueing], MatchingSet) -> ([Glueing], MatchingSet)
            addGlueings agentId2 (glueings, alreadyDone) = fromMaybe (glueings, alreadyDone) $
              do agent2 <- M.agentOfId agentId2 lhs
                 guard $ any (inLhs agent2) (Set.toList modifiedSites) -- check that lhs contains -ie tests- a site that is modified by the rule
                 m <- superpose [(agentId2, agentId1)] lhs rhs added env -- m: mixId -> ruleId
                 let (i, j) = Map.findMin m -- Jean uses Map.root here, but according to the OCaml Batteries Included sources Map.root is implemented as Map.findMin
                 guard $ Set.notMember (i, j) alreadyDone
                 return (m : glueings, Map.foldrWithKey (curry Set.insert) alreadyDone m)
              where
                inLhs :: Agent -> N.ModifiedSite -> Bool
                inLhs agent (siteId, int_lnk) = case M.siteDefined siteId agent of
                                                  Nothing -> False -- site not defined
                                                  Just (intState, lnkState) -> case int_lnk of
                                                                                 N.Int -> case intState of
                                                                                            Nothing -> False -- site can't be modified
                                                                                            Just _ -> True
                                                                                 N.Lnk -> case lnkState of
                                                                                            Unspecified -> False
                                                                                            _ -> True


