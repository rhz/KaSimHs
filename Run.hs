module Run where

import qualified RandomTree as RT
import qualified Injection as I
import qualified Dynamics as D
import qualified Counter as C
import qualified State as S
import qualified Env as E
import qualified Plot
import Misc

import System.Random (randomRIO)

event :: E.Env -> (S.State, C.Counter, Plot.Plot) -> IO (S.State, C.Counter, Plot.Plot, Bool) -- Bool is True if deadlocked
event env (state, counter, plot) =
  do -- 1. Time advance
     rnd <- randomRIO (0.0, 1.0)
     let totalActivity = RT.total $ S.activityTree state
         deadlock = totalActivity == 0
         dt = -(log rnd / totalActivity)
         counter' = C.incEvents $ C.incTime counter dt
     -- 2. Draw rule
     (ruleInj, state') <- S.drawRule state env
     -- 3. Apply rule, negative and positive update
     case ruleInj of
       Nothing -> return $! (state', C.incNullEvents counter', plot, deadlock)
       Just (rule, inj) -> let (state'', sideEffects, psi, isNullEvent) = S.apply state' rule inj env
                               counter'' = if isNullEvent
                                             then C.incNullEvents counter'
                                             else counter'
                               state''' = S.positiveUpdate state'' rule inj psi sideEffects env
                               plot' = Plot.add env state''' counter'' plot
                           in return $! (state''', counter'', plot', deadlock)

loop :: E.Env -> (S.State, C.Counter, Plot.Plot) -> IO (S.State, C.Counter, Plot.Plot, Bool) -- Bool is True if deadlocked
loop env (state, counter, plot) =
  if C.checkTime counter && C.checkEvents counter
    then do (state', counter', plot', deadlock) <- event env (state, counter, plot)
            if deadlock
              then return (state, counter, plot, True)
              else loop env (state',  counter', plot')
    else return (state, counter, plot, False)


