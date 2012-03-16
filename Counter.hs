module Counter where

type Time = Double
type Events = Int

data Counter = Counter{ time :: Time
                      , events :: Events
                      , nullEvents :: Events
                      , nullAction :: Int
                      , lastTick :: (Events, Time)
                      , initialized :: Bool
                      , ticks :: Int
                      , initTime :: Time
                      , initEvent :: Events
                      , maxTime :: Maybe Time
                      , maxEvents :: Maybe Events
                      , dT :: Maybe Time
                      , dE :: Maybe Events
                      }
  deriving (Show, Eq)

incTick :: Counter -> Counter
incTick c@(Counter{ ticks = t }) = c{ ticks = t+1 }

isInitial :: Counter -> Bool
isInitial (Counter{ time = t, initTime = t0 }) = t == t0

incTime :: Counter -> Time -> Counter
incTime c@(Counter{ time = t }) dt = c{ time = t + dt }

incEvents :: Counter -> Counter
incEvents c@(Counter{ events = e }) = c{ events = e+1 }

incNullEvents :: Counter -> Counter
incNullEvents c@(Counter{ nullEvents = ne }) = c{ nullEvents = ne+1 }

incNullAction :: Counter -> Counter
incNullAction c@(Counter{ nullAction = na }) = c{ nullAction = na+1 }

checkTime :: Counter -> Bool
checkTime (Counter{ time = t, maxTime = tmax }) = case tmax of
                                                    Nothing -> True
                                                    Just tmax -> t < tmax

checkEvents :: Counter -> Bool
checkEvents (Counter{ events = e, maxEvents = emax }) = case emax of
                                                          Nothing -> True
                                                          Just emax -> e < emax

setTick :: Counter -> (Events, Time) -> Counter
setTick c@(Counter{ lastTick = lastTick }) tick = c{ lastTick = tick }

lastIncrement :: Counter -> Time
lastIncrement (Counter{ time = t, lastTick = lastTick }) = t - lastTime
  where (_, lastTime) = lastTick

deltaTime :: Int -> Maybe Time -> Maybe Time
deltaTime numPoints maxTime = do tmax <- maxTime
                                 return $ tmax / fromIntegral numPoints

deltaEvents :: Int -> Maybe Events -> Maybe Events
deltaEvents numPoints maxEvent = do emax <- maxEvent
                                    return $ max (emax `div` numPoints) 1

create :: Time -> Events -> Maybe Time -> Maybe Events -> Int -> Counter
create initTime initEvent maxTime maxEvents numPoints =
  Counter{ time = initTime
         , initTime = initTime
         , maxTime = maxTime
         , events = initEvent
         , initEvent = initEvent
         , maxEvents = maxEvents
         , lastTick = (initEvent, initTime)
         , dT = deltaTime numPoints maxTime
         , dE = deltaEvents numPoints maxEvents
         , initialized = False
         , ticks = 0
         , nullEvents = 0
         , nullAction = 0
         }


