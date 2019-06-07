module Data.Graph.Causal where

import Prelude

import Data.Foldable (foldr)
import Data.Foldable as Foldable
import Data.Graph (Graph)
import Data.Graph as Graph
import Data.List (List(..))
import Data.List as List
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set

-- In theory, we could have a `Path` type guarded by a smart constructor to enforce that our
-- `List k` is actually a proper path. But a path only makes sense in the context of a graph,
-- so the `Path` type would have to carry around a copy of the graph too which sounds like a
-- hassle.
collider :: forall k v. Ord k => k -> List k -> Graph k v -> Boolean
collider k path g =
  Foldable.length (Graph.parents k g `Set.intersection` Set.fromFoldable path) == 2

isDSeparated :: forall k v. Ord k => k -> k -> Set k -> Graph k v -> Boolean
isDSeparated x y w g = Set.isEmpty $ dConnectedBy x y w g

isDConnected :: forall k v. Ord k => k -> k -> Set k -> Graph k v -> Boolean
isDConnected x y w g = not <<< Set.isEmpty $ dConnectedBy x y w g

dConnectedBy :: forall k v. Ord k => k -> k -> Set k -> Graph k v -> Set (List k)
dConnectedBy x y w g =
  Set.filter unblocked $ allUndirectedPaths x y g
  where
    unblocked path = nonCollidersDisjointFromW && collidersAncestorsOfW
      where
        { yes, no } = List.partition (\k -> collider k path g) path
        nonCollidersDisjointFromW = Set.isEmpty (Set.fromFoldable no `Set.intersection` w)
        collidersAncestorsOfW =
          Foldable.all
            (\k -> not <<< Set.isEmpty $
              Set.insert k (Graph.descendants k g) `Set.intersection` w)
            yes

dSeparated :: forall k v. Ord k => k -> Set k -> Graph k v -> Set k
dSeparated k w g =
  Set.filter (\v -> isDSeparated k v w g) <<< Set.delete k <<< Map.keys <<< Graph.toMap $ g

dConnected :: forall k v. Ord k => k -> Set k -> Graph k v -> Set k
dConnected k w g =
  Set.filter (\v -> isDConnected k v w g) <<< Set.delete k <<< Map.keys <<< Graph.toMap $ g

allUndirectedPaths :: forall k v. Ord k => k -> k -> Graph k v -> Set (List k)
allUndirectedPaths start end g = Set.map List.reverse $ go mempty start
  where
    go hist k =
      if end == k
      then Set.singleton hist'
      else
        if adjacent' == Set.empty
        then Set.empty
        else Foldable.foldMap (go hist') adjacent'
      where
        adjacent' = Graph.adjacent k g `Set.difference` Set.fromFoldable hist
        hist' = k `Cons` hist

instruments :: forall k v. Ord k => k -> k -> Set k -> Graph k v -> Set k
instruments x y w g = dConnected x w g `Set.intersection` dSeparated y w (intervene x g)

isInstrument :: forall k v. Ord k => k -> k -> k -> Set k -> Graph k v -> Boolean
isInstrument i x y w g = i `Set.member` instruments x y w g

intervene :: forall k v. Ord k => k -> Graph k v -> Graph k v
intervene k g = foldr removePointers g <<< Map.keys <<< Graph.toMap $ g
  where
    removePointers = Graph.alterEdges (map $ Set.filter (_ /= k))
