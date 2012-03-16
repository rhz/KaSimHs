module State where

import Prelude hiding (break)
import qualified Data.Vector as Vec
import qualified Data.Vector.Unboxed as Array
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Functor ((<$>))
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import System.Random (randomRIO)

import qualified Mixture as M
import qualified Node as N
import qualified SiteGraph as SG
import qualified Injection as I
import qualified InjectionVector as IV
import qualified Env as E
import qualified Counter as C
import qualified RandomTree as RT
import qualified Precondition as P
import Agent hiding (Free)
import Env (RuleId)
import Matching
import Dynamics
import Misc

-- TODO Replace (Set.Set Int) for IntSet and (Map.Map Int a) for (IntMap a) everywhere

type ComponentInjections = Vec.Vector (Maybe IV.InjVec)
type InjectionsTable = Vec.Vector (Maybe ComponentInjections)

type RuleMap = Map.Map RuleId Rule
type InfluenceMap = Map.Map RuleId (Map.Map M.MixtureId [Glueing]) -- source rule -> target rule (or observable) -> glueings
type LhsTable = Vec.Vector (Maybe M.Expr)
type Observables = [M.Expr]
type NumInstances = Int

data State = State{ siteGraph :: SG.SiteGraph
                  , injections :: InjectionsTable
                  , rules :: RuleMap
                  , observables :: Observables
                  , lhss :: LhsTable
                  , influenceMap :: InfluenceMap
                  , activityTree :: RT.RandomTree
                  , wakeUpMap :: P.Preconditions
                  }
  deriving (Show, Eq)


ruleOfId :: RuleId -> State -> Maybe Rule
ruleOfId id (State{ rules = rs }) = Map.lookup id rs

mixtureOfId :: M.MixtureId -> State -> Maybe M.Expr
mixtureOfId mixId (State{ lhss = lhss }) = join $ lhss Vec.!? mixId

-- Returns the number of instances of mixture mixId in implicit state
instanceNumber :: M.MixtureId -> State -> E.Env -> NumInstances
instanceNumber lhsId (State{ injections = injs }) env =
  if E.isEmptyLhs lhsId env
    then 1
    else fromCompInjs (join $ injs Vec.!? lhsId)
  where fromCompInjs Nothing = 0
        fromCompInjs (Just compInjs) = Vec.foldr fromInjs 1 compInjs
        fromInjs Nothing _ = 0
        fromInjs (Just injs) acc = acc * IV.size injs

-- Activities
-- Returns the evaluation of the activity (not divided by automorphisms) of the rule in implicit state 'state'
evalActivity :: Rule -> State -> E.Env -> Double
evalActivity (Rule{ oversampling = Just k }) _ _ = k
evalActivity (Rule{ k = k, ruleId = mixId }) state env = k * fromIntegral (instanceNumber mixId state env)

updateActivity :: E.Env -> RuleId -> State -> State
updateActivity env ruleId state@(State{ activityTree = activityTree }) =
  state{ activityTree = RT.add ruleId alpha activityTree }
  where rule = ruleOfId ruleId state ? "State.updateActivity: can't find rule indexed by rule id " ++ show ruleId
        alpha = evalActivity rule state env

-- Influence Map
buildInfluenceMap :: RuleMap -> LhsTable -> E.Env -> InfluenceMap
buildInfluenceMap rules patterns env = Map.foldrWithKey' addRule Map.empty rules
  where addRule :: RuleId -> Rule -> InfluenceMap -> InfluenceMap
        addRule ruleId rule im = Vec.ifoldr addPattern im patterns
          where addPattern :: M.MixtureId -> Maybe M.Expr -> InfluenceMap -> InfluenceMap
                addPattern _ Nothing im = im -- empty pattern
                addPattern mixId (Just mix) im = if null glueings
                                                   then im
                                                   else addInfluence ruleId mixId glueings im
                  where glueings = enable rule mix env -- glueings: [phi_0,...,phi_n] partial embeddings list

        addInfluence :: RuleId -> M.MixtureId -> [Glueing] -> InfluenceMap -> InfluenceMap
        addInfluence ruleId mixId glueings im = Map.insert ruleId (Map.insert mixId glueings m) im
          where m = Map.findWithDefault Map.empty ruleId im

enabled :: Rule -> State -> Map.Map RuleId [Glueing]
enabled (Rule{ lhs = lhs }) (State{ influenceMap = im }) = Map.findWithDefault Map.empty ruleId im
  where ruleId = M.getId lhs ? "State.enabled: rule without id"

{-
dotOfInfluence :: InfluenceMap -> State -> E.Env -> String
dotOfInfluence influenceMap state env = 
-}

-- Embeddings
-- Compute complete embedding of mix into sg at given root for initialization phase
generateEmbeddings :: SG.SiteGraph -> N.NodeId -> M.Expr -> ComponentInjections -> (SG.SiteGraph, ComponentInjections)
generateEmbeddings sg anchorNodeId mix@(M.Expr{ M.rootOfCc = rootOfCc }) compInjs =
  iter 0 sg compInjs
  where iter :: M.ComponentId -> SG.SiteGraph -> ComponentInjections -> (SG.SiteGraph, ComponentInjections)
        iter ccId sg compInjs = 
          if ccId == arity
            then (sg, compInjs) -- no more components (complexes) to try to embed
            else case embedding of
                   Nothing -> iter (ccId+1) sg compInjs -- we couldn't embed on this one
                   Just (sg', compInjs') -> iter (ccId+1) sg' compInjs' -- we could, and proceed
          where embedding = do agentRootId <- rootOfCc Vec.!? ccId
                               -- portMap: nodeId -> [({Int,Lnk}, siteId), ...] if port siteId of node nodeId is int/lnk-tested by map
                               (inj, portMap) <- component Map.empty agentRootId sg anchorNodeId mix True Set.empty
                               let ccIdInjs = fromMaybe (IV.create IV.defaultInjVecSize)
                                                        (compInjs Vec.!? ccId ? "State.generateEmbeddings: injections for component are missing")
                                   (injId, ccIdInjs') = IV.alloc inj ccIdInjs
                                   compInjs' = updateVec compInjs [(ccId, Just ccIdInjs')] "State.generateEmbeddings"
                               return (SG.addLift (mixId, ccId, injId) portMap sg, compInjs')

        mixId = M.getId mix ? "State.generateEmbeddings: mixture has no id"
        arity = M.arity mix ? "State.generateEmbeddings: mixture's arity has not been computed"

initializeEmbeddings :: State -> [M.Expr] -> State
initializeEmbeddings state@(State{ siteGraph = sg }) lhss = SG.ifoldl' embeddingsAt state sg
  where
    embeddingsAt state nodeId _ = foldr (tryEmbeddingAt nodeId) state lhss

    tryEmbeddingAt :: N.NodeId -> M.Expr -> State -> State
    tryEmbeddingAt nodeId lhs state@(State{ siteGraph = sg, injections = injs }) =
      state{ injections = updateVec injs [(lhsId, Just compInjs')] "State.initializeEmbeddings"
           , siteGraph = sg'
           }
      where lhsId = M.getId lhs ? "State.initializeEmbeddings: lhs has no id"
            arity = M.arity lhs ? "State.initializeEmbeddings: lhs's arity has not been computed"
            compInjs = fromMaybe (Vec.replicate arity Nothing)
                                 (injs Vec.!? lhsId ? "State.initializeEmbeddings: mixture id " ++ show lhsId ++ " not found in injection map")
            -- Complement the embeddings of lhs in sg using node nodeId as anchor for matching
            (sg', compInjs') = generateEmbeddings sg nodeId lhs compInjs

-- Initialise (I'll keep the original function names which are in american english)
initialize :: SG.SiteGraph -> [Rule] -> Observables -> E.Env -> State
initialize sg rules obs env = state'{ activityTree = Map.foldrWithKey initActivity (activityTree state') ruleMap }
  where state = State{ siteGraph = sg
                     , injections = Vec.replicate dim_mixs Nothing
                     , rules = ruleMap
                     , observables = obs
                     , lhss = lhsTable
                     , influenceMap = influenceMap
                     , activityTree = RT.createTree $ length rules
                     , wakeUpMap = wakeUpTable
                     }
        mixs = map lhs rules ++ obs
        dim_mixs = length mixs
        lhsTable = updateVec (Vec.replicate dim_mixs Nothing) (map mixWithId $ filter (not . M.null) mixs) "State.initialize"
        ruleMap = foldr addRule Map.empty rules
        wakeUpTable = foldr P.insert P.empty mixs -- initialise wake up map for side effects
        influenceMap = buildInfluenceMap ruleMap lhsTable env

        state' = initializeEmbeddings state mixs

        mixWithId :: M.Expr -> (M.MixtureId, Maybe M.Expr)
        mixWithId lhs = (lhsId, Just lhs)
          where lhsId = M.getId lhs ? "State.initialize: no id for lhs"

        addRule :: Rule -> RuleMap -> RuleMap
        addRule rule@(Rule{ ruleId = rId }) = Map.insert rId rule

        initActivity :: RuleId -> Rule -> RT.RandomTree -> RT.RandomTree
        initActivity rId rule = RT.add rId activity
          where activity = evalActivity rule state' env


-- Random
-- Returns an array Vec.fromList [inj_0,...,inj_k] where arity(r) == k containing
-- one random injection per connected component of lhs(r)
selectInjection :: State -> M.Expr -> MaybeT IO I.InjectionMap -- Monad transformers
selectInjection state lhs = if M.null lhs
                              then lift $ return Map.empty
                              else do (embedding, _) <- Vec.foldM addInjHeap (Map.empty, Set.empty) compInjs
                                      return embedding
  where lhsId = M.getId lhs ? "State.selectInjection: lhs doesn't have an assigned id"
        compInjs = join (injections state Vec.!? lhsId) ? "State.selectInjection: variable " ++ show lhsId ++ " has no instances but a positive activity"

        addInjHeap :: (I.InjectionMap, N.NodeSet) -> Maybe IV.InjVec -> MaybeT IO (I.InjectionMap, N.NodeSet)
        addInjHeap _ Nothing = error "State.selectInjection: invalid argument"
        addInjHeap (totalInj, totalCod) (Just injHeap) = MaybeT $ do inj <- IV.random injHeap
                                                                     return $ I.codomain inj (totalInj, totalCod)

-- Draw a rule at random in the state according to its activity
drawRule :: State -> E.Env -> IO (Maybe (Rule, I.InjectionMap), State)
drawRule state env =
  do (lhsId, tree') <- RT.random $ activityTree state
     let state' = state{ activityTree = tree' }
     case lhsId of
       Nothing -> return (Nothing, state')
       Just ruleId -> do let rule = ruleOfId ruleId state ? "State.drawRule: rule not found"
                         (state'', isNullEvent) <- correctTree ruleId rule state'
                         ruleInj <- runMaybeT $ do guard $ not isNullEvent
                                                   embedding <- selectInjection state'' (lhs rule)
                                                   return (rule, embedding)
                         return (ruleInj, state'')
  where
    correctTree :: RuleId -> Rule -> State -> IO (State, Bool)
    correctTree ruleId rule state@(State{ activityTree = tree }) =
      if alpha /= infinity && alpha > approxAlpha -- approxAlpha is an overestimation of alpha, so it must be bigger than alpha
        then error $ "State.drawRule: activity invariant violation (" ++ show alpha ++ " > " ++ show approxAlpha ++ ") " ++ show tree
        else do rnd <- randomRIO (0.0, 1.0)
                if rnd > alpha / approxAlpha -- we correct the tree only is the difference is big enough
                  then return (state{ activityTree = RT.add ruleId alpha tree' }, True) -- correct over-approximation of activity
                  else return (state{ activityTree = tree' }, False)
      where (approxAlphaMaybe, tree') = RT.weightOfNode tree ruleId
            approxAlpha = approxAlphaMaybe ? "State.drawRule: activity not found in tree"
            alpha = evalActivity rule state env


-- Updates
type VisitedMap = Map.Map M.MixtureId MatchingSet
type WakeUpMap = Map.Map N.NodeId MatchingSet -- FIXME WakeUpMap seems not to be a good name, as the wakeUpMap in State has type Precondition
type Modifs = Set.Set (N.NodeId, N.PortId)
data IntLnk = Int | Lnk | Both

wakeUp :: State -> IntLnk -> Modifs -> WakeUpMap -> E.Env -> WakeUpMap
wakeUp state@(State{ siteGraph = sg }) modifType modifs wuMap env = Set.foldr addModif wuMap modifs
  where addModif :: (N.NodeId, SiteId) -> WakeUpMap -> WakeUpMap
        addModif (nodeId, siteId) wuMap =
          case SG.nodeOfId nodeId sg of
            Nothing -> wuMap
            -- Add pairs (mixId, ccId) to the potential new matches to be tried at anchor nodeId
            Just node -> Map.insert nodeId (oldCandidates `Set.union` newCandidates node) wuMap
          where oldCandidates = Map.findWithDefault Set.empty nodeId wuMap

                newCandidates node = P.findAll (N.nameId node) siteId (int modifType) (lnk modifType) (isFree modifType) (wakeUpMap state)
                  where int Lnk = Nothing -- Lnk means internal state must not be taken into account
                        int _ = N.internalState node siteId

                        lnk Int = Nothing -- Int means binding state must not be taken into account
                        lnk _ = case N.follow node siteId of
                                  Nothing -> error "State.wakeUp: couldn't find a neighbour"
                                  Just (nodeId', siteId') -> let name' = N.nameId (SG.nodeOfId nodeId' sg ? "State.wakeUp: neighbour id is not in site graph")
                                                             in Just (name', siteId') -- TODO is name' the same nodeId'?

                        isFree Int = False -- this is weird
                        isFree _ = not $ N.isBound node siteId

{- TODO this is for updating algebraic expression, not needed yet
-- circular dependencies would blow this up
updateDeps :: E.Env -> E.DepType -> State -> State
updateDeps env dep@(E.KappaDep i) state = Set.foldr (updateDeps env) state deps -- no need to update kappa observable, it will be updated if plotted
  where deps = E.getDeps dep env ? "State.updateDeps: could not find dependencies of kappa variable " ++ show i
updateDeps env dep@(E.RuleDep ruleId) state = Set.foldr (updateDeps env) state' deps
  where deps = E.getDeps dep env ? "State.updateDeps: could not find dependencies of rule " ++ show ruleId
        state' = updateActivity env ruleId state
-}

-- Positive updates
findNewInjs :: State -> M.MixtureId -> M.Expr -> M.ComponentId -> N.NodeId -> AgentId -> VisitedMap -> E.Env -> (State, VisitedMap)
findNewInjs state@(State{ injections = injs, siteGraph = sg }) mixId mix ccId nodeId rootId alreadyDone env =
  case component Map.empty rootId sg nodeId mix True rootNodeSet of
    Nothing -> (state, alreadyDone) -- no new embedding was found
    Just (inj, portMap) -> -- new embedding
      let (injId, ccIdInjs') = IV.alloc inj ccIdInjs
          compInjs' = updateVec compInjs [(ccId, Just ccIdInjs')] "State.findNewInjs"
          state' = state{ injections = updateVec injs [( mixId, Just compInjs' )] "State.findNewInjs"
                        , siteGraph = SG.addLift (mixId, ccId, injId) portMap sg
                        }
          state'' = if E.isRule mixId env
                      then updateActivity env mixId state'
                      else state'
      in (state'', alreadyDone')
  where
    mixId = M.getId mix ? "State.findNewInjs: mixture has no id"
    rootNodeSet = Map.findWithDefault Set.empty mixId alreadyDone
    compInjs = fromMaybe (Vec.replicate (M.arity mix ? "State.findNewInjs: arity not available") Nothing)
                         (injs Vec.!? mixId ? "State.findNewInjs: injections not found for var " ++ show mixId)
    ccIdInjs = fromMaybe (IV.create IV.defaultInjVecSize)
                         (compInjs Vec.!? ccId ? "State.findNewInjs: injection not found")
    alreadyDone' = Map.insert mixId (Set.insert (rootId, nodeId) rootNodeSet) alreadyDone

positiveUpdate :: State -> Rule -> I.InjectionMap -> I.InjectionMap -> Modifs -> E.Env -> State
positiveUpdate state rule phi psi sideModifs env =
  if not $ sideEffects rule
    then state'
    else state'' -- handle side effects
  where varsToWakeUp = enabled rule state
        (state', alreadyDone) = Map.foldrWithKey wakeUpRule (state, Map.empty) varsToWakeUp -- alreadyDone map is empty because glueings are guaranteed to be different by construction

        -- Influence map tells me to look for new injections of mixture mixId
        wakeUpRule :: RuleId -> [Glueing] -> (State, VisitedMap) -> (State, VisitedMap)
        wakeUpRule mixId glueings (state, alreadyDone) = foldr wakeUpGlueing (state, alreadyDone) glueings
          where wakeUpGlueing :: Glueing -> (State, VisitedMap) -> (State, VisitedMap)
                wakeUpGlueing glueing (state, alreadyDone) = findNewInjs state mixId lhs ccId nodeId lhsId alreadyDone env
                  where (lhsId, rhsId) = Map.findMin glueing -- Jean uses Map.root here... see Dynamics.hs
                        nodeId = if Set.member rhsId $ added rule
                                   then Map.lookup rhsId psi ? "State.positiveUpdate: looking for image of agent " ++ show rhsId ++ " in embedding " ++ show psi
                                   else Map.lookup rhsId phi ? "State.positiveUpdate: looking for image of agent " ++ show rhsId ++ " in embedding " ++ show phi
                        lhs = join (lhss state Vec.!? mixId) ? "State.positiveUpdate: mixture " ++ show mixId ++ " not found"
                        ccId = M.componentOfId lhsId lhs ? "State.positiveUpdate: component " ++ show lhsId ++ " not found"

        wuMap = wakeUp state Int sideModifs Map.empty env
        --wuMap' = wakeUp state Lnk pertIntro wuMap env
        (state'', _) = Map.foldrWithKey inspectSideEffect (state', alreadyDone) wuMap

        -- Side effect on node nodeId forces me to look for new embedding
        inspectSideEffect :: N.NodeId -> MatchingSet -> (State, VisitedMap) -> (State, VisitedMap)
        inspectSideEffect nodeId candidates (state@(State{ siteGraph = sg }), alreadyDone) = Set.foldr findAnchors (state, alreadyDone) candidates
          where nodeName = N.nameId (SG.nodeOfId nodeId sg ? "State.positiveUpdate: node not found")
                
                findAnchors :: (RuleId, M.ComponentId) -> (State, VisitedMap) -> (State, VisitedMap)
                findAnchors (mixId, ccId) (state, alreadyDone) = Set.foldr newInjs (state, alreadyDone) possibleRoots
                  where possibleRoots = M.idsOfName (nodeName, ccId) lhs
                        lhs = join (lhss state Vec.!? mixId) ? "State.positiveUpdate: mixture " ++ show mixId ++ " not found"

                        newInjs :: AgentId -> (State, VisitedMap) -> (State, VisitedMap)
                        newInjs rootId (state, alreadyDone) = findNewInjs state mixId lhs ccId nodeId rootId alreadyDone env


-- Negative updates
-- Removes all injections pointed by lifts --if they still exist
removeInjs :: E.Env -> (N.NodeId, SiteId) -> N.IntOrLnk -> State -> State
removeInjs env (nodeId, portId) int_lnk state@(State{ siteGraph = sg }) = state'
  where node = SG.nodeOfId nodeId sg ? "State.removeInjs: node " ++ show nodeId ++ " not found"
        liftset = N.getLift int_lnk node portId ? "State.removeInjs: oops" -- liftset: injections where a site plays a role

        -- TODO what to do with this?
        --lift' = Set.filter (not . I.isTrashed) lift
        --node' = N.setLift int_lnk node portId lift'
        --state' = state{ siteGraph = SG.replaceNode sg nodeId node' }

        state' = Set.foldr removeInj state liftset

        removeInj :: N.Lift -> State -> State
        removeInj lift@(mixId, ccId, injId) state@(State { injections = injs }) = --state'{ injections = injs' }
          -- TODO is this updateActivity useful?
          if E.isRule mixId env
            then updateActivity env mixId state'{ injections = injs' }
            else state'{ injections = injs' }
          where mix = mixtureOfId mixId state ? "State.removeInjs: mixture " ++ show mixId ++ " not found"

                state' = Map.foldrWithKey removeInjFromNodeDeps state phi

                compInjs = join (injs Vec.!? mixId) ? "State.removeInjs: rule was applied with no injection"
                injCcId = join (compInjs Vec.!? ccId) ? "State.removeInjs: rule was applied when a component had no injection"
                phi = injCcId IV.!? injId ? "State.removeInjs: injection " ++ show injId ++ " not found"

                injCcId' = IV.remove injId injCcId
                compInjs' = updateVec compInjs [(ccId, Just injCcId')] "State.removeInjs"
                injs' = updateVec injs [(mixId, Just compInjs')] "State.removeInjs"

                removeInjFromNodeDeps :: AgentId -> N.NodeId -> State -> State
                removeInjFromNodeDeps agentId nodeId state = foldInterface removeDep state agent
                  where agent = M.agentOfId agentId mix ? "State.removeInjs: agent " ++ show agentId ++ " not found"

                        removeDep :: SiteId -> Site -> State -> State
                        removeDep siteId (int, lnk) state@(State{ siteGraph = sg }) = state{ siteGraph = SG.replaceNode sg nodeId node' }
                          where node  = SG.nodeOfId nodeId sg ? "State.removeInjs: Node " ++ show nodeId ++ " is no longer in the graph and injection " ++ show injId ++ " of mixture " ++ show mixId ++ " was pointing to it!"
                                node' = N.setLifts node siteId (updateIntLifts int intLifts, updateLnkLifts lnk lnkLifts)
                                (intLifts, lnkLifts) = N.getLifts node siteId ? "State.removeInjs: oops"

                                updateIntLifts Nothing = id
                                updateIntLifts _ = Set.delete lift

                                updateLnkLifts Unspecified = id
                                updateLnkLifts _ = Set.delete lift

negativeUpdate :: State -> (N.NodeId, SiteId) -> IntLnk -> E.Env -> State
negativeUpdate state (nodeId, portId) Int  env = removeInjs env (nodeId, portId) N.Int state
negativeUpdate state (nodeId, portId) Lnk  env = removeInjs env (nodeId, portId) N.Lnk state
negativeUpdate state (nodeId, portId) Both env = removeInjs env (nodeId, portId) N.Int $ removeInjs env (nodeId, portId) N.Lnk state

-- Rule application
-- bind allow for looping bond
bind :: State -> (N.NodeId, N.PortId) -> (N.NodeId, N.PortId) -> Modifs -> E.Env -> (State, Modifs)
bind state@(State{ siteGraph = sg }) (u, i) (v, j) sideEffects env = (state''', sideEffects')
  where node_u = SG.nodeOfId u sg ? "State.bind: node not found"
        node_v = SG.nodeOfId v sg ? "State.bind: node not found"
        (_, ptr_u_i) = N.getStatus node_u i ? "State.bind: agent " ++ show u ++ " has no site " ++ show i
        (_, ptr_v_j) = N.getStatus node_v j ? "State.bind: agent " ++ show v ++ " has no site " ++ show j

        (state'@(State{ siteGraph = sg' }), sideEffects') = setNbPtr ptr_v_j $ setNbPtr ptr_u_i (state, sideEffects)
        
        setNbPtr :: N.Ptr -> (State, Modifs) -> (State, Modifs)
        setNbPtr (N.FPtr _ _) _ = error "State.bind: invalid argument"
        setNbPtr (N.Ptr nbId nbPortId) (state@(State{ siteGraph = sg }), sideEffects) = (state', sideEffects')
          where sideEffects' = Set.insert (nbId, nbPortId) sideEffects
                nb = SG.nodeOfId nbId sg ? "State.bind: neighbour node not found"
                nb' = N.setPtr nb nbPortId N.Null
                sg' = SG.replaceNode sg nbId nb'
                state' = negativeUpdate state{ siteGraph = sg' } (nbId, nbPortId) Lnk env
        setNbPtr N.Null (state, sideEffects) = (state, sideEffects)

        node_u' = N.setPtr node_u i (N.Ptr v j)
        node_v' = N.setPtr node_v j (N.Ptr u i)
        state''  = negativeUpdate state'{  siteGraph = SG.replaceNode sg'  u node_u' } (u, i) Lnk env
        state''' = negativeUpdate state''{ siteGraph = SG.replaceNode sg'' v node_v' } (v, j) Lnk env
        sg'' = siteGraph state''

break :: State -> (AgentId, SiteId) -> Modifs -> Bool -> E.Env -> (State, Modifs, Bool) -- Bool is True if null event
break state@(State{ siteGraph = sg }) (nodeId, portId) sideEffects sideEffectFree env =
  case N.getPtr node portId ? "State.break: agent " ++ show nodeId ++ " has no site " ++ show portId of
    N.Null -> (state, sideEffects, True)
    N.Ptr nbId nbPortId -> let nb = SG.nodeOfId nbId sg ? "State.break: node " ++ show nbId ++ " not found (neighbour)"
                               sg' = SG.replaceNodes sg [ (nodeId, N.setPtr node portId N.Null)
                                                        , (nbId, N.setPtr nb nbPortId N.Null)
                                                        ]
                               state' = negativeUpdate state{ siteGraph = sg' } (nodeId, portId) Lnk env
                               state'' = negativeUpdate state' (nbId, nbPortId) Lnk env
                           in if sideEffectFree
                                then (state'', sideEffects, False)
                                else (state'', Set.insert (nbId, nbPortId) sideEffects, False)
    N.FPtr _ _ -> error "State.break: invalid argument"
  where
    node = SG.nodeOfId nodeId sg ? "State.break: node " ++ show nodeId ++ " not found"

-- modify is always side-effects free
modify :: State -> (AgentId, SiteId) -> InternalStateId -> E.Env -> (State, Bool) -- Bool is True if null event
modify state@(State{ siteGraph = sg }) (nodeId, portId) intStateId env =
  case N.getInt node portId ? "State.modify: agent " ++ show nodeId ++ " has no site " ++ show portId of
    Nothing -> error $ "State.modify: node " ++ show nodeId ++ " has no internal state to modify"
    Just i -> (state', i == intStateId)
  where
    state' = negativeUpdate state{ siteGraph = sg' } (nodeId, portId) Int env
    sg' = SG.replaceNode sg nodeId node'
    node = SG.nodeOfId nodeId sg ? "State.modify: node " ++ show nodeId ++ " not found"
    node' = N.setInt node portId (Just intStateId)

delete :: State -> AgentId -> Modifs -> E.Env -> (State, Modifs)
delete state@(State{ siteGraph = sg }) nodeId sideEffects env = N.foldStatus updateSite (state, sideEffects) node
  where
    node = SG.nodeOfId nodeId sg ? "State.delete: node " ++ show nodeId ++ " not found"

    updateSite :: (State, Modifs) -> N.PortId -> N.PortStatus -> (State, Modifs)
    updateSite _ _ (_, N.FPtr _ _) = error "State.delete: invalid argument"
    updateSite (state, sideEffects) portId (_, N.Null)              = (negativeUpdate state (nodeId, portId) Both env, sideEffects)
    updateSite (state, sideEffects) portId (_, N.Ptr nbId nbPortId) = (state''', Set.insert (nbId, nbPortId) sideEffects)
      where
        state'   = negativeUpdate state   (nodeId, portId) Both env
        state''' = negativeUpdate state'' (nbId, nbPortId) Lnk  env
        state''  = state'{ siteGraph = SG.replaceNode sg' nbId nb' }
        sg' = siteGraph state'
        nb  = SG.nodeOfId nbId sg' ? "State.break: node " ++ show nbId ++ " not found (neighbour)"
        nb' = N.setPtr nb nbPortId N.Null


apply :: State -> Rule -> I.InjectionMap -> E.Env -> (State, Modifs, I.InjectionMap, Bool) -- Bool is True if null event
apply state rule phi env = foldr edit (state, Set.empty, Map.empty, False) (script rule)
  where app :: I.InjectionMap -> I.InjectionMap -> Id -> Maybe N.NodeId
        app _ psi (Fresh i) = Map.lookup i psi
        app phi _ (Kept  i) = Map.lookup i phi
  
        edit :: Action -> (State, Modifs, I.InjectionMap, Bool) -> (State, Modifs, I.InjectionMap, Bool)
        edit (Bnd (agentId1, siteId1) (agentId2, siteId2)) (state, sideEffects, psi, isNullEvent) =
          (state', sideEffects', psi, isNullEvent)
          where u = app phi psi agentId1 ? "State.apply: node not found"
                v = app phi psi agentId2 ? "State.apply: node not found"
                (state', sideEffects') = bind state (u, siteId1) (v, siteId2) sideEffects env

        edit (Brk (agentId, siteId) sideEffectFree) (state, sideEffects, psi, isNullEvent) =
          (state', sideEffects', psi, isNullEvent' || isNullEvent)
          where nodeId = app phi psi agentId ? "State.apply: node not found"
                (state', sideEffects', isNullEvent') = break state (nodeId, siteId) sideEffects sideEffectFree env

        edit (Mod (agentId, siteId) intStateId) (state, sideEffects, psi, isNullEvent) =
          (state', sideEffects, psi, isNullEvent' || isNullEvent)
          where nodeId = app phi psi agentId ? "State.apply: node not found"
                (state', isNullEvent') = modify state (nodeId, siteId) intStateId env

        edit (Del agentId) (state, sideEffects, psi, isNullEvent) =
          (state'{ siteGraph = sg'' }, sideEffects', psi, isNullEvent)
          where nodeId = Map.lookup agentId phi ? "State.apply: node not found"
                (state'@(State{ siteGraph = sg' }), sideEffects') = delete state nodeId sideEffects env
                sg'' = SG.removeNode sg' nodeId

        edit (Add agentId nameId) (state@(State{ siteGraph = sg }), sideEffects, psi, isNullEvent) =
          (state{ siteGraph = sg' }, sideEffects, Map.insert agentId nodeId psi, isNullEvent)
          where node = N.createNode nameId Nothing env
                (sg', nodeId) = SG.addNode sg node


