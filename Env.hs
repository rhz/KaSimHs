module Env( Env, emptyEnv -- env
          , numOfAgent, declareAgent, nameNumber -- agents
          , RuleId, numOfRule, ruleOfNum, declareRule, isRule -- rules
          , VarId, VarName, declareVar, varOfNum -- vars
          , sig, idOfSite, siteOfId, idOfState, stateOfId, declareSig, getSig -- signatures
          , declareEmptyLhs, isEmptyLhs -- lhs
--          , DepType(..), DepSet, DepMap, addDep, removeDep, getDeps -- dep graph
          ) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Vector as Vec

import KappaParser (AgentName, RuleName, SiteName, InternalState)
import Agent
import Signature
import Misc

type VarId = Int
type RuleId = Int
type VarName = String

{- TODO this is for updating algebraic expressions, not needed yet
-- Dep Graph
data DepType = KappaDep VarId
             | RuleDep RuleId
  deriving (Show, Eq, Ord)
type DepSet = Set.Set DepType
type DepMap = Map.Map DepType DepSet
-}

-- Environment
data Env = Env{ signatures :: Vec.Vector Sig

              , freshNameId :: AgentNameId
              , numOfName_ :: Map.Map AgentName AgentNameId
              , nameOfNum_ :: Vec.Vector AgentName

              , numOfRule_ :: Map.Map RuleName RuleId
              , ruleOfNum_ :: Map.Map RuleId RuleName

              , numOfVar_ :: Map.Map VarName VarId
              , varOfNum_ :: Map.Map VarId VarName
              , freshVarId :: VarId

--              , dependencies :: DepMap

              , ruleIndices :: Set.Set RuleId -- what is this for?
              , emptyLhs :: Set.Set RuleId -- and this?
              }
  deriving (Show, Eq)

emptyEnv :: Env
emptyEnv = Env{ signatures = Vec.empty
              , freshNameId = 0
              , numOfName_ = Map.empty
              , nameOfNum_ = Vec.empty
              , numOfRule_ = Map.empty
              , ruleOfNum_ = Map.empty
              , numOfVar_ = Map.empty
              , varOfNum_ = Map.empty
              , freshVarId = 0
--              , dependencies = Map.empty
              , ruleIndices = Set.empty
              , emptyLhs = Set.empty
              }

name :: AgentNameId -> Env -> Maybe AgentName
name id (Env {nameOfNum_ = nn}) = nn Vec.!? id

numOfAgent :: AgentName -> Env -> Maybe AgentNameId
numOfAgent name (Env {numOfName_ = nn}) = Map.lookup name nn

numOfRule :: RuleName -> Env -> Maybe RuleId
numOfRule ruleName (Env {numOfRule_ = nr}) = Map.lookup ruleName nr

ruleOfNum :: RuleId -> Env -> Maybe RuleName
ruleOfNum id (Env {ruleOfNum_ = rn}) = Map.lookup id rn

declareAgent :: AgentName -> Env -> (Env, AgentNameId)
declareAgent name env@(Env {nameOfNum_ = nameOfNum, numOfName_ = numOfName, freshNameId = id}) =
  if Map.member name numOfName
    then error $ "Agent '" ++ name ++ "' is defined twice"
    else (env{nameOfNum_ = Vec.snoc nameOfNum name,
              numOfName_ = Map.insert name id numOfName,
              freshNameId = id + 1}, id)

nameNumber :: Env -> Int
nameNumber (Env {nameOfNum_ = nn}) = Vec.length nn

declareRule :: RuleName -> RuleId -> Env -> Env
declareRule ruleName id env@(Env {numOfRule_ = numOfRule, ruleOfNum_ = ruleOfNum}) =
  if Map.member ruleName numOfRule
    then error $ "Rule name '" ++ ruleName ++ "' is already used"
    else env{ numOfRule_ = Map.insert ruleName id numOfRule
            , ruleOfNum_ = Map.insert id ruleName ruleOfNum
            }

isRule :: RuleId -> Env -> Bool
isRule ruleId = Set.member ruleId . ruleIndices

declareVar :: Bool -> Maybe VarName -> Env -> (Env, VarId)
declareVar fromRule nameOpt env@(Env{ freshVarId = id, numOfVar_ = np, varOfNum_ = pn, ruleIndices = ri }) =
  case Map.lookup name np of
    Just _ -> error $ "Label '" ++ show name ++ "' already defined"
    Nothing -> (env', id)
  where env' = env{ ruleIndices = if fromRule
                                    then Set.insert id ri
                                    else ri
                  , numOfVar_ = Map.insert name id np
                  , varOfNum_ = Map.insert id name pn
                  , freshVarId = id+1
                  }
        name = fromMaybe ("%anonymous" ++ show id) nameOpt

varOfNum :: Env -> VarId -> Maybe VarName
varOfNum (Env{ varOfNum_ = von }) varId = Map.lookup varId von

sig :: AgentName -> Env -> Maybe Sig
sig agentName (Env {signatures = sigs, numOfName_ = numOfName}) =
  do n <- Map.lookup agentName numOfName
     sigs Vec.!? n

idOfSite :: AgentName -> SiteName -> Env -> Maybe SiteId
idOfSite agentName siteName env =
  do sign <- sig agentName env
     numOfSite siteName sign

siteOfId :: AgentName -> SiteId -> Env -> Maybe SiteName
siteOfId agentName id env =
  do sign <- sig agentName env
     siteOfNum id sign

idOfState :: AgentName -> SiteName -> InternalState -> Env -> Maybe InternalStateId
idOfState agentName siteName state env =
  do sign <- sig agentName env
     siteId <- numOfSite siteName sign
     numOfInternalState siteId state sign

stateOfId :: AgentName -> SiteName -> InternalStateId -> Env -> Maybe InternalState
stateOfId agentName siteName stateId env =
  do sign <- sig agentName env
     siteId <- numOfSite siteName sign
     internalStateOfNum siteId stateId sign

declareSig :: Sig -> Env -> Env
declareSig sign env@(Env {signatures = sigs}) =
  if id < Vec.length sigs
    then error "Signature already defined"
    else env{signatures = Vec.snoc sigs sign}
  where id = sigId sign

getSig :: AgentNameId -> Env -> Maybe Sig
getSig agentNameId (Env {signatures = sigs}) = sigs Vec.!? agentNameId

declareEmptyLhs :: RuleId -> Env -> Env
declareEmptyLhs id env@(Env {emptyLhs = e}) = env{emptyLhs = Set.insert id e}

isEmptyLhs :: RuleId -> Env -> Bool -- fn looking for a better name
isEmptyLhs id (Env {emptyLhs = e}) = Set.member id e

{- TODO this is for updating algebraic expressions, not needed yet
--- Dep Graph
addDep :: DepType -> DepType -> Env -> Env
addDep dep dep' env@(Env{ dependencies = deps }) = env{ dependencies = Map.insert dep (Set.insert dep' set) deps }
  where set = Map.findWithDefault Set.empty dep deps

removeDep :: DepType -> DepType -> Env -> Env
removeDep dep dep' env@(Env{ dependencies = deps }) = env{ dependencies = Map.insert dep (Set.delete dep' set) deps }
  where set = Map.findWithDefault Set.empty dep deps

getDeps :: DepType -> Env -> Maybe DepSet
getDeps dep env = Map.lookup dep (dependencies env)
-}

