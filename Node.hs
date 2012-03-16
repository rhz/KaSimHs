module Node where

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Vector as Vec

import qualified Agent as A
import Mixture (MixtureId, ComponentId)
import Injection
import qualified Env as E
import Signature
import Misc

type NodeId = Int
type NodeSet = Set.Set NodeId

type Lift = (MixtureId, ComponentId, InjectionId)
type LiftSet = Set.Set Lift
type Dep = (LiftSet, LiftSet) -- (lifts for int, lifts for lnk)

type PortId = Int -- same as A.SiteId
type PortStatus = (Maybe A.InternalStateId, Ptr) -- (internal state, link state)
data Port = Port { status :: PortStatus
                 , dep :: Dep
                 }
  deriving (Show, Eq)

type Interface = Vec.Vector Port
data Node = Node { nameId :: A.AgentNameId
                 , interface :: Interface
                 , nodeAddress :: Maybe NodeId
                 }
  deriving (Show, Eq)

data Ptr = Null
         | Ptr NodeId Int -- we use NodeId instead of Node, because in a functional language you should only keep references
         | FPtr Int Int
  deriving (Show, Eq)

data IntOrLnk = Int | Lnk
  deriving (Show, Eq, Ord)
type ModifiedSite = (PortId, IntOrLnk)
type PortList = [ModifiedSite]

-- exported types
type PortMap = Map.Map NodeId PortList
type NodeMap = Map.Map NodeId Node

getLifts :: Node -> PortId -> Maybe (LiftSet, LiftSet)
getLifts node portId = do port <- interface node Vec.!? portId
                          return $ dep port

setLifts :: Node -> PortId -> (LiftSet, LiftSet) -> Node
setLifts node portId value = node{ interface = updateVec intf [(portId, port{ dep = value })] "Node.setLifts" }
  where intf = interface node
        port = intf Vec.!? portId ? "Node.setLifts: port " ++ show portId ++ " not found in node's interface"

getLift :: IntOrLnk -> Node -> PortId -> Maybe LiftSet
getLift Int node portId = do port <- interface node Vec.!? portId
                             return . fst $ dep port
getLift Lnk node portId = do port <- interface node Vec.!? portId
                             return . snd $ dep port

setLift :: IntOrLnk -> Node -> PortId -> LiftSet -> Node
setLift int_lnk node portId liftset' = node{ interface = updateVec intf [(portId, port{ dep = liftsets })] "Node.setLift" }
  where intf = interface node
        port = intf Vec.!? portId ? "Node.setLift: port " ++ show portId ++ " not found in node's interface"
        (liftsetInt, liftsetLnk) = dep port
        liftsets = case int_lnk of
                     Int -> (liftset', liftsetLnk)
                     Lnk -> (liftsetInt, liftset')

foldStatus :: (a -> PortId -> PortStatus -> a) -> a -> Node -> a
foldStatus f seed node = Vec.ifoldl' g seed (interface node)
  where g acc portId port = f acc portId (status port)

{-
foldDep :: (PortId -> (LiftSet, LiftSet) -> a -> a) -> a -> Node -> a
foldDep f seed node = Vec.ifoldr (\portId port a -> f portId (dep port) a) seed (interface node)

foldInterface :: (PortId -> Port -> a -> a) -> a -> Node -> a
foldInterface f seed node = Vec.ifoldr f seed (interface node)
-}

getStatus :: Node -> PortId -> Maybe PortStatus
getStatus node portId = do port <- interface node Vec.!? portId
                           return $ status port

getPtr :: Node -> PortId -> Maybe Ptr
getPtr node portId = liftM snd $ getStatus node portId

getInt :: Node -> PortId -> Maybe (Maybe A.InternalStateId)
getInt node portId = liftM fst $ getStatus node portId

internalState :: Node -> PortId -> Maybe A.InternalStateId
internalState node portId = do port <- interface node Vec.!? portId
                               fst $ status port

isBound :: Node -> PortId -> Bool
isBound node portId =
  case status (interface node Vec.!? portId ? "Node.isBound: port not found") of
    (_, FPtr _ _) -> error "Node.isBound: invalid argument"
    (_, Null) -> False
    (_, Ptr u j) -> True

setPtr :: Node -> PortId -> Ptr -> Node
setPtr node portId value = node{ interface = updateVec intf [(portId, port{ status = (intState, value) })] "Node.setPtr" }
  where intf = interface node
        port = intf Vec.!? portId ? "Node.setPtr: port " ++ show portId ++ " not found in node's interface"
        (intState, _) = status port

setInt :: Node -> PortId -> Maybe A.InternalStateId -> Node
setInt node portId value = node{ interface = updateVec intf [(portId, port{ status = (value, lnkState) })] "Node.setInt" }
  where intf = interface node
        port = intf Vec.!? portId ? "Node.setInt: port " ++ show portId ++ " not found in node's interface"
        (_, lnkState) = status port

createNode :: A.AgentNameId -> Maybe A.Interface -> E.Env -> Node
createNode nameId intf env = Node{ nameId = nameId, interface = interface, nodeAddress = Nothing }
  where sign = E.getSig nameId env ? "Node.createNode: signature not found"
        interface = Vec.generate (arity sign) addSite
        addSite siteId = Port{ status = (intState, Null), dep = (Set.empty, Set.empty) }
          where intState = case intf >>= Map.lookup siteId of
                             Just (state, _) -> state
                             Nothing -> Just 0 -- TODO why is this? existential site?

addDep :: Node -> PortId -> IntOrLnk -> Lift -> Node
addDep node portId int_lnk lift = node{ interface = updateVec intf [(portId, port{ dep = dep' })] "Node.addDep" }
  where intf = interface node
        port = intf Vec.!? portId ? "Node.addDep: port " ++ show portId ++ " not found in node's interface"
        dep' = add lift int_lnk (dep port)

        add :: Lift -> IntOrLnk -> Dep -> Dep
        add lift Int (ints, lnks) = (Set.insert lift ints, lnks)
        add lift Lnk (ints, lnks) = (ints, Set.insert lift lnks)

addDeps :: Node -> Lift -> PortList -> Node
addDeps node lift = foldr addPort node
  where addPort :: ModifiedSite -> Node -> Node
        addPort (portId, int_lnk) node = addDep node portId int_lnk lift

allocate :: Node -> NodeId -> Node
allocate node nodeId = node{ nodeAddress = Just nodeId }

-- Tests whether status of port portId of node nodeId is compatible with (int, lnk)
-- If it's not compatible returns Nothing
-- If it is then we return (Int, portId) if the port is int-tested and (Lnk, portId) if it's lnk-tested
test :: (Node, PortId) -> A.Site -> PortList -> Maybe PortList
test (node, portId) (int, lnk) portList =
  do portList' <- case int of
                    Nothing -> return portList -- wildcard in pattern is compatible with anything in the node
                    s -> do guard $ s == state
                            return $ (portId, Int):portList
     testLink lnk link portList'
  where (state, link) = status (interface node Vec.!? portId ? "Node.test: port " ++ show portId ++ " not found in node's interface")

        testLink :: A.BindingState -> Ptr -> PortList -> Maybe PortList
        testLink A.Unspecified _ portList' = return portList' -- wildcard in pattern is compatible with anything in the node

        testLink A.Bound (FPtr _ _) _ = error $ "Node.test: invalid status for bound node " ++ show node ++ " and site " ++ show portId
        testLink A.Bound (Ptr _ _) portList' = return $ (portId, Lnk):portList'
        testLink A.Bound Null _ = Nothing

        testLink A.Free (FPtr _ _) _ = error $ "Node.test: invalid status for free node " ++ show node ++ " and site " ++ show portId
        testLink A.Free (Ptr _ _) _ = Nothing
        testLink A.Free Null portList' = return $ (portId, Lnk):portList'

        testLink A.SemiLink _ _ = error "Node.test: a node should not have semilinks"

follow :: Node -> PortId -> Maybe (NodeId, PortId)
follow node portId = case getPtr node portId ? "Node.follow: node " ++ show node ++ " have no site " ++ show portId of
                       Ptr v j -> Just (v, j)
                       _ -> Nothing


