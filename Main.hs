module Main where

import qualified KappaParser as KP
import qualified Mixture as M
import qualified Plot as P
import qualified Counter as C
import qualified State as S
import qualified Eval
import qualified Env
import Run

import System.Environment (getArgs)
import Control.Monad (mapM_)
import Data.Maybe (fromJust)

readKappaFile :: String -> IO (Env.Env, S.State)
readKappaFile filename =
  do fileContents <- readFile filename
     let ast = KP.parseKappaFile fileContents
     return $ Eval.initialize ast

-- TODO #haskell: I've just finished to port an ocaml code to haskell and it's about 10 times slower =(

main :: IO ()
main = do filename:maxEventsStr:maxTimeStr:numPointsStr:_ <- getArgs
          (env, state) <- readKappaFile filename
          let maxTime = if read maxTimeStr == 0
                          then Nothing
                          else Just $ read maxTimeStr
              maxEvents = if read maxEventsStr == 0
                            then Nothing
                            else Just $ read maxEventsStr
              counter = C.create 0 0 maxTime maxEvents (read numPointsStr)
              plot = P.create env state
              obsNames = map (fromJust . Env.varOfNum env . fromJust . M.getId) (S.observables state)
          (state', counter', plot', deadlock) <- loop env (state, counter, plot)
          putStrLn $ "Deadlock = " ++ show deadlock
          putStrLn $ "#Time Events " ++ unwords obsNames
          mapM_ (putStrLn . showPoint) plot'
  where
    showPoint :: (C.Time, C.Events, P.Observations) -> String
    showPoint (time, events, obs) = show time ++ " " ++ show events ++ " " ++ unwords (map (show . snd) obs)


