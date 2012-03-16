module RandomTree(RandomTree(..), Activity, total, weightOfNode, createTree, add, random) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Vector as Vec
import qualified Data.Vector.Unboxed as Array
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import System.Random (randomRIO)
import Misc
import Env

{-- What's the idea of a RandomTree?
 -- Which operations is it optmized for?
 -- I'm sure in Haskell there must be a better way to get that performance
 -- -}

-- TODO this smells like finger trees

type Activity = Double
type LayerId = Int
type MaskId = Int
type Layer = Array.Vector LayerId

data RandomTree = RandomTree{ mask_ :: Map.Map RuleId MaskId -- RuleId -> MaskId
                            , unmask_ :: Map.Map MaskId RuleId
                            , newMask :: RuleId
                            , infSet :: Set.Set MaskId -- this are the ids of the rules that have infinite activity (weird concept)
                            , size :: Int
                            , total_ :: Activity -- total activity
                            , weightOfNodes :: Array.Vector Activity -- activity of each rule -- MaskId -> Activity
                            , weightOfSubtrees :: Array.Vector Activity -- partial activity of the subtree -- MaskId -> Activity
                            , unbalancedEventsByLayer :: Vec.Vector [Int] -- LayerId -> [MaskId]
                            , unbalancedEvents :: Array.Vector Bool -- MaskId -> isBalanced?
                            , layer :: Layer -- MaskId -> LayerId
                            , consistent :: Bool
                            }
  deriving (Show, Eq)

mask :: RandomTree -> RuleId -> (MaskId, RandomTree)
mask tree@(RandomTree{ newMask = m, mask_ = mask, unmask_ = unmask }) i = lookupOrInsert $ Map.lookup i mask
  where lookupOrInsert (Just x) = (x, tree)
        lookupOrInsert Nothing = (m, tree{ newMask = m+1
                                         , mask_ = Map.insert i m mask
                                         , unmask_ = Map.insert m i unmask
                                         })

unmask :: RandomTree -> MaskId -> Maybe RuleId
unmask tree m = Map.lookup m $ unmask_ tree

total :: RandomTree -> Activity
total (RandomTree{ infSet = infSet, total_ = total }) = if Set.null infSet
                                                          then total
                                                          else infinity

weightOfNode :: RandomTree -> RuleId -> (Maybe Activity, RandomTree)
weightOfNode tree ruleId = (weightOfNodes tree Array.!? maskId, tree')
  where (maskId, tree') = mask tree ruleId

updateStructure :: RandomTree -> RandomTree
updateStructure tree@(RandomTree{ size = size }) = if consistent tree
                                                     then tree
                                                     else tree'{ consistent = True }
  where tree' = foldl' (flip updateLayer) tree [nLayer,nLayer-1..1]
        nLayer = layer tree Array.!? size ? "RandomTree.updateStructure: mask id " ++ show size ++ " not found"

        updateLayer :: LayerId -> RandomTree -> RandomTree
        updateLayer layerId tree@(RandomTree{ unbalancedEventsByLayer = uebl }) = foldl' (flip updateSubtree) tree' unbalancedSubtrees
          
          where tree' = tree{ unbalancedEventsByLayer = updateVec uebl [(layerId, [])] "RandomTree.updateStructure" }
                unbalancedSubtrees = uebl Vec.!? layerId ? "RandomTree.updateStructure: layer id " ++ show layerId ++ " not found"

                updateSubtree :: MaskId -> RandomTree -> RandomTree
                updateSubtree maskId tree@(RandomTree{ weightOfSubtrees = ss
                                                     , unbalancedEvents = ues
                                                     , weightOfNodes = ns
                                                     }) =
                  if maskId == 1 -- is root?
                    then tree'
                    else declareUnbalanced parent tree'

                  where tree' = tree{ weightOfSubtrees = ss Array.// [(maskId, weight)]
                                    , unbalancedEvents = ues Array.// [(maskId, False)]
                                    }
                        weight = node + weightOf (2*maskId) + weightOf (2*maskId+1)
                        node = ns Array.!? maskId ? "RandomTree.updateStructure: mask id " ++ show maskId ++ " not found"

                        weightOf maskId = fromMaybe 0 (ss Array.!? maskId)

                        parent = quot maskId 2

declareUnbalanced :: MaskId -> RandomTree -> RandomTree
declareUnbalanced maskId tree@(RandomTree{ unbalancedEvents = ue, unbalancedEventsByLayer = uebl, layer = layer }) =
  tree'{ consistent = False }
  where tree' = if ue Array.!? maskId ? "RandomTree.declareUnbalanced: mask id " ++ show maskId ++ " not found"
                  then tree
                  else tree{ unbalancedEvents = ue Array.// [(maskId, True)],
                             unbalancedEventsByLayer = updateVec uebl [(layerId, maskId : unbalancedSubtrees)] "RandomTree.declareUnbalanced" }
        layerId = layer Array.!? maskId ? "RandomTree.declareUnbalanced: mask id " ++ show maskId ++ " not found"
        unbalancedSubtrees = uebl Vec.!? layerId ? "RandomTree.declareUnbalanced: layer id " ++ show layerId ++ " not found"

createTree :: Int -> RandomTree
createTree n = RandomTree{ size = n
                         , total_ = 0
                         , newMask = 1
                         , mask_ = Map.empty
                         , unmask_ = Map.empty
                         , infSet = Set.empty
                         , consistent = True
                         , weightOfNodes = Array.replicate (n+1) 0 -- TODO why +1? what's the first element for?
                         , weightOfSubtrees = Array.replicate (n+1) 0
                         , unbalancedEvents = Array.replicate (n+1) False
                         , unbalancedEventsByLayer = Vec.replicate (n+1) []
                         , layer = genLayers 1 1 1 (Array.replicate (n+1) 0)
                         }
  where genLayers :: MaskId -> LayerId -> LayerId -> Layer -> Layer
        genLayers maskId currentLayer layerEnd layer
            | maskId > n = layer
            | maskId > layerEnd = genLayers maskId (currentLayer+1) (2*layerEnd+1) layer
            | otherwise = genLayers (maskId+1) currentLayer layerEnd layer'
          where layer' = layer Array.// [(maskId, currentLayer)]

--raz :: RandomTree -> RandomTree -- TODO what's this function for? it's defined but not used in KaSim

add :: RuleId -> Double -> RandomTree -> RandomTree
add ruleId activity tree@(RandomTree{ total_ = total, weightOfNodes = nws, infSet = infSet }) =
  declareUnbalanced maskId tree'{ total_ = total - oldActivity + newActivity
                                , weightOfNodes = nws Array.// [(maskId, newActivity)]
                                , infSet = infSet'
                                }
  where (maskId, tree') = mask tree ruleId
        (newActivity, infSet') = if activity == infinity
                                   then (0.0,       Set.insert maskId infSet)
                                   else (activity,  Set.delete maskId infSet)
        oldActivity = nws Array.!? maskId ? "RandomTree.add: mask id " ++ show maskId ++ " not found"

random :: RandomTree -> IO (Maybe RuleId, RandomTree)
random tree = case infRuleId of
                Nothing -> ruleAndTree
                id -> return (id, tree)
  where
    infRuleId = do (infRule, _) <- Set.minView $ infSet tree
                   unmask tree infRule

    ruleAndTree | totalActivity == 0.0 = return (Nothing, tree')
                | otherwise = do rnd <- randomRIO (0.0, totalActivity)
                                 let i = do rep <- find 1 rnd tree' -- start looking at mask id 1 (ie, the first rule)
                                            unmask tree' rep
                                 return (i, tree')

    tree' = updateStructure tree
    totalActivity = weightOfSubtrees tree' Array.!? 1 ? "RandomTree.random: mask id 1 not found"

find :: MaskId -> Double -> RandomTree -> Maybe MaskId
find maskId rnd tree@(RandomTree{ size = size })
    | rnd < nodeActivity = Just maskId
    | lchild > size = Nothing
    | rnd' < left = find lchild rnd' tree
    | rchild > size = Nothing
    | otherwise = find rchild (rnd' - left) tree
  where
    rnd' = rnd - nodeActivity
    nodeActivity = weightOfNodes tree Array.!? maskId ? "RandomTree.find: mask id " ++ show maskId ++ " not found"
    left = weightOfSubtrees tree Array.!? lchild ? "RandomTree.find: subtree not found"
    lchild = 2 * maskId
    rchild = lchild + 1


