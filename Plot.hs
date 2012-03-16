module Plot where

import qualified Mixture as M
import qualified Counter as C
import qualified State as S
import qualified Env as E
import Misc

type Observations = [(E.VarId, S.NumInstances)]
type Plot = [(C.Time, C.Events, Observations)]

obs :: E.Env -> S.State -> Observations
obs env state@(S.State{ S.observables = obs }) = map numInstances obs
  where numInstances :: M.Expr -> (E.VarId, S.NumInstances)
        numInstances mix = (mixId, S.instanceNumber mixId state env)
          where mixId = M.getId mix ? "Plot.obs: no id for observable"

create :: E.Env -> S.State -> Plot
create env initialState = [(0, 0, obs env initialState)]

add :: E.Env -> S.State -> C.Counter -> Plot -> Plot
add env state (C.Counter{ C.time = currentTime, C.events = currentEvent, C.dE = dE, C.dT = dT }) plot =
  if isStep dE dT
    then (currentTime, currentEvent, obs env state) : plot
    else plot
  where isStep Nothing Nothing = error "Plot.add: dT and dE missing"
        isStep (Just dE) _ = currentEvent - lastEvent == dE -- preference is given to dE
        isStep _ (Just dT) = currentTime - lastTime == dT

        (lastTime, lastEvent, _) = head plot

--save :: String -> Plot -> IO ()
--save filename plot = 


