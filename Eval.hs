module Eval where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Vector as Vec
import Data.Monoid

import qualified KappaParser as KP
import Agent
import qualified Mixture as M
import Dynamics
import Signature
import Env
import qualified Node as N
import qualified SiteGraph as SG
import qualified State as S
import Misc

{-- This module compiles the Abstract Syntax Tree (created by KappaParser) into the specialized data structures used to run a simulation.
 -- Those data structures are defined in the modules Agent, Mixture, Dynamics, Signature, Node, SiteGraph and Env.
 -- Agent, Mixture and Dynamics define agents, expressions and rules, respectively, when they form patterns.
 -- On the other hand, Node and SiteGraph define agents and expressions when they are part of a reaction mixture.
 -- -}

-- Rules and patterns
type PortMap = Map.Map KP.SiteName (KP.InternalState, KP.BindingState)

evalIntf :: KP.Interface -> PortMap
evalIntf = foldr insertSite Map.empty
  where insertSite :: KP.Site -> PortMap -> PortMap
        insertSite (KP.Site siteName internalState bindingState) m =
          if Map.member siteName m
            then error $ "Site '" ++ siteName ++ "' is used multiple times"
            else Map.insert siteName (internalState, bindingState) m

evalAgent :: Bool -> KP.Agent -> Env -> M.Context -> (Agent, M.Context)
evalAgent isPattern agent@(KP.Agent name intf) env ctxt = (Agent nameId interface, ctxt')
  where
    nameId = numOfAgent name env ? "Agent '" ++ name ++ "' is not declared"
    sign = getSig nameId env ? "Agent '" ++ name ++ "' is not declared"
    portMap = evalIntf intf
    (interface, ctxt') = Map.foldrWithKey addSite (Map.empty, ctxt) portMap

    addSite :: KP.SiteName -> (KP.InternalState, KP.BindingState) -> (Interface, M.Context) -> (Interface, M.Context)
    addSite siteName (state, link) (intf, ctxt@(M.Context {M.currId = id, M.pairing = p})) = evalLink link
      where
        siteId = numOfSite siteName sign ? "Site '" ++ siteName ++ "is not defined for agent '" ++ name ++ "'"
        stateId = if state == "" then Nothing
                    else Just (numOfInternalState siteId state sign ? "Internal state '" ++ state ++ "is not defined for site '" ++ siteName ++ "' in agent '" ++ name ++ "'")

        evalLink :: KP.BindingState -> (Interface, M.Context)
        evalLink (KP.Bound n) =
          case Map.lookup n p of
            Just (M.Link b j) -> (Map.insert siteId (stateId, Bound) intf,
                                ctxt{ M.pairing = Map.insert n M.Closed p,
                                      M.newEdges = Map.insert (id, siteId) (b, j) (M.newEdges ctxt) })
            Just M.Closed -> error $ "Edge identifier " ++ show n ++ " is used too many times"
            Nothing -> (Map.insert siteId (stateId, Bound) intf,
                        ctxt{ M.pairing = Map.insert n (M.Link id siteId) p })

        evalLink KP.SemiLink =
          if isPattern
            then (Map.insert siteId (stateId, SemiLink) intf, ctxt)
            else error "Illegal use of '_' in concrete graph definition"

        evalLink KP.Unspecified =
          if isPattern
            then (Map.insert siteId (stateId, SemiLink) intf, ctxt)
            else error "Illegal use of '?' in concrete graph definition"

        evalLink KP.Free = (Map.insert siteId (stateId, Free) intf, ctxt)

evalMixture :: Bool -> Maybe M.MixtureId -> Env -> KP.Expr -> M.Expr
evalMixture isPattern mixId env expr =
  case check $ M.pairing ctxt' of
    Nothing -> M.setRootOfCc . M.enumAlternateAnchors $ mix
    Just n -> error $ "Edge identifier " ++ show n ++ " is not paired"
  where ctxt = M.Context{ M.pairing = Map.empty, M.currId = 0, M.newEdges = Map.empty }
        (ctxt', mix) = foldr addAgent (ctxt, M.emptyExpr mixId) expr

        addAgent :: KP.Agent -> (M.Context, M.Expr) -> (M.Context, M.Expr)
        addAgent a (ctxt, mix) = (ctxt'{ M.currId = id+1, M.newEdges = Map.empty },
                                  M.compose id agent mix ne)
          where (agent, ctxt'@(M.Context {M.currId = id, M.newEdges = ne})) = evalAgent isPattern a env ctxt

        check :: M.PairingMap -> Maybe Int
        check p = getFirst $ Map.foldrWithKey (\k v m -> mappend (findSemiLink k v) m) mempty p
        findSemiLink n (M.Link _ _) = First $ Just n
        findSemiLink _ M.Closed = mempty

evalSignature :: KP.Sig -> Env -> (Sig, Env)
evalSignature (KP.Sig name intf) env = (createSig nameId intf, env')
  where (env', nameId) = declareAgent name env

evalRule :: KP.Rule -> Env -> (Rule, Env)
evalRule (KP.Rule name lhs rhs rate) env = (rule, env''')
  where rule = Rule{ k = rate
                   , oversampling = Nothing
                   , lhs = lhsMix
                   , rhs = rhsMix
                   , ruleId = lhsId
                   , script = script
                   , balance = balance
                   , added = added
                   , sideEffects = sideEffects
                   , modifiedSites = modifSites
                   }
        (env', lhsId) = declareVar True (Just name) env
        env'' = declareRule name lhsId env'
        env''' = if M.null lhsMix
                   then declareEmptyLhs lhsId env''
                   else env''
        lhsMix = evalMixture True (Just lhsId) env''' lhs
        rhsMix = evalMixture True Nothing env''' rhs
        (script, balance, added, modifSites, sideEffects) = diff lhsMix rhsMix env'''

evalRules :: [KP.Decl] -> Env -> ([Rule], Env)
evalRules rs env = (reverse rules, env') -- TODO does it matter if it's in the reverse order?
  where (rules, env') = foldr addRule ([], env) rs
        addRule (KP.RuleDecl r) (rules, env) = (rule:rules, env')
          where (rule, env') = evalRule r env
        addRule _ (rules, env) = (rules, env)

-- Obs
evalObs :: [KP.Decl] -> Env -> (S.Observables, Env)
evalObs decls env = foldr addObs ([], env) decls
  where addObs (KP.Obs varName expr) (obs, env) = (evalMixture True (Just obsId) env expr : obs, env')
          where (env', obsId) = declareVar False (Just varName) env
        addObs _ (obs, env) = (obs, env)

-- Init
type LinkMap = Map.Map KP.BondLabel (AgentId, SiteId)
type Bond = (AgentId, SiteId, AgentId, SiteId)

evalNode :: Env -> N.NodeId -> KP.Agent -> (N.NodeMap, LinkMap) -> (N.NodeMap, LinkMap)
evalNode env nodeId (KP.Agent name intf) (nodeMap, linkMap) = (foldr addBond nodeMap' bonds, linkMap')
  where nameId = numOfAgent name env ? "Eval.evalNode: agent '" ++ name ++ "' is not declared"
        sign = getSig nameId env ? "Eval.evalNode: agent '" ++ name ++ "' is not declared"
        (bonds, linkMap', interface) = buildIntf intf linkMap Map.empty []

        buildIntf :: KP.Interface -> LinkMap -> Interface -> [Bond] -> ([Bond], LinkMap, Interface)
        buildIntf [] linkMap interface bonds = (bonds, linkMap, interface)
        buildIntf (KP.Site siteName intState lnkState : intf) linkMap interface bonds =
          buildIntf intf linkMap' (Map.insert siteId (internalState, Unspecified) interface) bonds'
          where siteId = numOfSite siteName sign ? "Eval.evalNode: site '" ++ siteName ++ "' is not declared"
                internalState = if intState == ""
                                  then Nothing
                                  else numOfInternalState siteId intState sign
                (linkMap', bonds') = evalLnk lnkState

                evalLnk (KP.Bound i) = (Map.delete i linkMap, (nodeId, siteId, nodeId', siteId'):bonds)
                  where (nodeId', siteId') = Map.lookup i linkMap ? "Eval.evalNode: edge identifier at site '" ++ siteName ++ "' is used multiple times"
                evalLnk KP.Free = (linkMap, bonds)
                evalLnk _ = error $ "Eval.evalNode: site '" ++ siteName ++ "' is partially defined"

        node = N.createNode nameId (Just interface) env
        nodeMap' = Map.insert nodeId node nodeMap

        addBond :: Bond -> N.NodeMap -> N.NodeMap
        addBond (ni, pi, nj, pj) nodeMap = Map.insert ni node_i' (Map.insert nj node_j' nodeMap)
          where node_i = Map.lookup ni nodeMap ? "Eval.eval_node"
                node_j = Map.lookup nj nodeMap ? "Eval.eval_node"
                node_i' = N.setPtr node_i pi (N.Ptr nj pj)
                node_j' = N.setPtr node_j pj (N.Ptr ni pi)

evalNodes :: KP.Expr -> Env -> N.NodeMap
evalNodes expr env = if Map.null linkMap
                       then nodeMap
                       else error $ "Eval.evalNodes: Dangling edge identifiers: " ++ show (Map.keys linkMap)
  where (nodeMap, linkMap) = foldr (uncurry $ evalNode env) (Map.empty, Map.empty) (zip [0..] expr)

evalInit :: [KP.Decl] -> Env -> SG.SiteGraph
evalInit decls env = foldr addInit (SG.createGraph SG.defaultGraphSize) decls
  where addInit :: KP.Decl -> SG.SiteGraph -> SG.SiteGraph
        addInit (KP.Init n expr) sg = foldr (\_ sg -> SG.addNodes sg nodes) sg [0..n-1] -- add nodes n times
          where nodes = evalNodes expr env
        addInit _ sg = sg

-- Environment and Signatures
environmentOfAst :: [KP.Decl] -> Env
environmentOfAst = foldr addSig emptyEnv
  where addSig (KP.SigDecl sign) env = uncurry declareSig $ evalSignature sign env
        addSig _ env = env

initialize :: [KP.Decl] -> (Env, S.State)
initialize decls = (env'', S.initialize sg rules obs env'')
  where env = environmentOfAst decls
        sg = evalInit decls env
        (rules, env') = evalRules decls env
        (obs, env'') = evalObs decls env'


