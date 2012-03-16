module Agent( KP.SiteName, SiteId, KP.InternalState, InternalStateId, BindingState(..), Site, Interface
            , AgentId, AgentNameId, Agent(..), KP.AgentName, nameId, interface, foldInterface
            ) where

import qualified KappaParser as KP
import qualified Data.Map as Map
import qualified Data.Vector as Vec

{- Basic types regarding Kappa agents and some accessor functions.
 -}

-- Sites
type SiteId = Int
type InternalStateId = Int
data BindingState = Free | SemiLink | Bound | Unspecified -- WLD = Unspecified
  deriving (Show, Eq)
type Site = (Maybe InternalStateId, BindingState)
type Interface = Map.Map SiteId Site

-- Agents
type AgentId = Int
type AgentNameId = Int
data Agent = Agent AgentNameId Interface
  deriving (Show, Eq)

nameId (Agent agentNameId _) = agentNameId
interface (Agent _ intf) = intf

foldInterface :: (SiteId -> Site -> a -> a) -> a -> Agent -> a
foldInterface f acc (Agent _ intf) = Map.foldrWithKey f acc intf

