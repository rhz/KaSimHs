module Signature where

import qualified Data.Map as Map
import qualified Data.Vector as Vec
import Data.List(intercalate)

import qualified KappaParser as KP
import Agent
import Misc

-- Types
type SiteBimap = (Vec.Vector SiteName, Map.Map SiteName SiteId)
type InternalStateBimap = (Vec.Vector InternalState, Map.Map InternalState InternalStateId)
data Sig = Sig AgentNameId SiteBimap (Vec.Vector InternalStateBimap)
  deriving (Show, Eq)

sigId :: Sig -> AgentNameId
sigId (Sig agentNameId _ _) = agentNameId

createSig :: AgentNameId -> KP.SigIntf -> Sig
createSig nameId sigSites = Sig nameId sites internalStates
  where sites = bimap siteNames
        siteNames = map extractName sigSites
        extractName (KP.SigSite name _) = name
        internalStates = Vec.fromList $ map internalState sigSites
        internalState (KP.SigSite _ internalStates) = bimap internalStates
        bimap xs = (Vec.fromList xs, Map.fromList $ zip xs [0..])

numOfSite :: SiteName -> Sig -> Maybe SiteId
numOfSite siteName (Sig _ (_, siteNum) _) = Map.lookup siteName siteNum

siteOfNum :: SiteId -> Sig -> Maybe SiteName
siteOfNum i (Sig _ (siteNames, _) _) = siteNames Vec.!? i

addSite :: SiteName -> Sig -> Sig
addSite siteName (Sig nameId (siteNames, siteNum) internalStates) =
  Sig nameId
      (Vec.snoc siteNames siteName, Map.insert siteName (Map.size siteNum) siteNum)
      (Vec.snoc internalStates (Vec.empty, Map.empty))

addInternalState :: InternalState -> SiteId -> Sig -> Sig
addInternalState state siteId (Sig nameId sites internalStates) =
  -- Update internalStates at index siteId
  Sig nameId sites (updateVec internalStates [(siteId, (stateVec', stateMap'))] "Signature.addInternalState")
  where stateVec' = Vec.snoc stateVec state
        stateMap' = Map.insert state (Map.size stateMap) stateMap
        (stateVec, stateMap) = internalStates Vec.!? siteId ? "Signature.addInternalState: site " ++ show siteId ++ " not found"

numOfInternalState :: SiteId -> InternalState -> Sig -> Maybe InternalStateId
numOfInternalState siteId state (Sig _ _ internalStates) =
  do (_, stateMap) <- internalStates Vec.!? siteId
     Map.lookup state stateMap

internalStateOfNum :: SiteId -> InternalStateId -> Sig -> Maybe InternalState
internalStateOfNum siteId stateId (Sig _ _ internalStates) =
  do (stateVec, _) <- internalStates Vec.!? siteId
     stateVec Vec.!? stateId

defaultInternalState :: SiteId -> Sig -> InternalState
defaultInternalState siteId (Sig _ _ internalStates) = Vec.head stateVec
  where (stateVec, _) = internalStates Vec.!? siteId ? "Signature.defaultInternalState: site " ++ show siteId ++ " not found"

internalStateNumber :: SiteId -> Sig -> Int
internalStateNumber siteId (Sig _ _ internalStates) = Vec.length stateVec
  where (stateVec, _) = internalStates Vec.!? siteId ? "Signature.addInternalState: site " ++ show siteId ++ " not found"

arity :: Sig -> Int
arity (Sig _ (siteNames, _) _) = Vec.length siteNames

toString :: Sig -> String
toString (Sig nameId (siteNames, _) internalStates) = show nameId ++ "(" ++ intfStr ++ ")"
  where intfStr = intercalate ", " intf
        intf = Vec.toList $ Vec.imap showSite siteNames

        showSite siteId name = show name ++ showStates (internalStates Vec.!? siteId ? "Signature.addInternalState: site " ++ show siteId ++ " not found")
        showStates (stateVec, _) = concat . Vec.toList $ Vec.map ("~" ++) stateVec

-- Implicit Signature
-- I'll take another approach to implicit signatures: output a Kappa file with the signatures inferred from
-- the rules and the initial mixture. So, the inferred signatures can be reviewed by users and developers,
-- making the debugging of this feature easier.

type SigMap = Map.Map KP.AgentName KP.Sig

inferSigs :: [KP.Decl] -> [KP.Decl]
inferSigs decls = map KP.SigDecl (Map.elems sigmap) ++ decls
  where sigmap = foldr updateSig Map.empty agents
        agents = concatMap extractAgents decls

        extractAgents :: KP.Decl -> [KP.Agent]
        extractAgents (KP.Init _ expr) = expr
        extractAgents (KP.RuleDecl (KP.Rule _ lhs rhs _)) = lhs ++ rhs
        extractAgents _ = []

        updateSig :: KP.Agent -> SigMap -> SigMap
        updateSig (KP.Agent name intf) sigmap = Map.insert name (KP.Sig name sigIntf) sigmap
          where sigIntf = case Map.lookup name sigmap of
                            Nothing -> map siteToSig intf -- add signature -- also foldr addIntState (KP.Sig name []) intf
                            Just (KP.Sig _ sigIntf) -> foldr addIntState sigIntf intf -- update signature

        siteToSig :: KP.Site -> KP.SigSite
        siteToSig (KP.Site siteName intState _) = KP.SigSite siteName [intState]

        addIntState :: KP.Site -> KP.SigIntf -> KP.SigIntf
        addIntState (KP.Site siteName intState _) = map updateSite
          where updateSite sigSite@(KP.SigSite sigSiteName intStates) =
                  if siteName == sigSiteName && intState `notElem` intStates
                    then KP.SigSite sigSiteName (intState:intStates) -- or (intStates ++ [intState])
                    else sigSite

