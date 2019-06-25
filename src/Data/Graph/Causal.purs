module Data.Graph.Causal where

import Prelude

import Data.Foldable (foldr)
import Data.Foldable as Foldable
import Data.Graph (Graph)
import Data.Graph as Graph
import Data.Graph.Causal.Utility (after, before, distinctTwoSets)
import Data.List.NonEmpty (NonEmptyList)
import Data.List.NonEmpty as NEL
import Data.List.Types (nelCons)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.TwoSet (TwoSet(..))

-- In theory, we could have a `Path` type guarded by a smart constructor to enforce that our
-- `List k` is actually a proper path. But a path only makes sense in the context of a graph,
-- so the `Path` type would have to carry around a copy of the graph too which sounds like a
-- hassle.
collider :: forall k v. Ord k => k -> NonEmptyList k -> Graph k v -> Boolean
collider k path g =
  Foldable.any (\a -> isParent a k g) (after k path) &&
  Foldable.any (\b -> isParent b k g) (before k path)
  where
    isParent p c g' = p `Set.member` Graph.parents c g'

areDConnected :: forall k v. Ord k => TwoSet k -> Set k -> Graph k v -> Boolean
areDConnected ks conditionedOn g = not <<< Set.isEmpty $ dConnectedBy ks conditionedOn g

dConnectedBy :: forall k v. Ord k => TwoSet k -> Set k -> Graph k v -> Set (NonEmptyList k)
dConnectedBy ks conditionedOn g =
  Set.filter unblocked $ allUndirectedPaths ks g
  where
    unblocked path = nonCollidersDisjointFromW && collidersAncestorsOfW
      where
        { yes, no } = NEL.partition (\k -> collider k path g) path
        nonCollidersDisjointFromW =
          Set.isEmpty (Set.fromFoldable no `Set.intersection` conditionedOn)
        collidersAncestorsOfW =
          Foldable.all
            (\k -> not <<< Set.isEmpty $
              Set.insert k (Graph.descendants k g) `Set.intersection` conditionedOn)
            yes

dConnectedTo :: forall k v. Ord k => k -> Set k -> Graph k v -> Set k
dConnectedTo k conditionedOn g =
  Set.filter (\v -> areDConnected (MkTwoSet k v) conditionedOn g) <<<
  Set.delete k <<< Map.keys <<< Graph.toMap $ g

areDSeparated :: forall k v. Ord k => TwoSet k -> Set k -> Graph k v -> Boolean
areDSeparated ks conditionedOn g = Set.isEmpty $ dConnectedBy ks conditionedOn g

dSeparatedFrom :: forall k v. Ord k => k -> Set k -> Graph k v -> Set k
dSeparatedFrom k conditionedOn g =
  Set.filter (\v -> areDSeparated (MkTwoSet k v) conditionedOn g) <<<
  Set.delete k <<< Map.keys <<< Graph.toMap $ g

dSeparations :: forall k v. Ord k => Set k -> Graph k v -> Set (TwoSet k)
dSeparations conditionedOn g =
  Set.filter (\ks -> areDSeparated ks conditionedOn g) <<<
  distinctTwoSets <<<
  Map.keys <<< Graph.toMap $ g

allUndirectedPaths :: forall k v. Ord k => TwoSet k -> Graph k v -> Set (NonEmptyList k)
allUndirectedPaths (MkTwoSet start end) g = Set.map NEL.reverse $ go Nothing start
  where
    go hist k =
      if end == k
      then Set.singleton hist'
      else
        if adjacent' == Set.empty
        then Set.empty
        else Foldable.foldMap (go $ Just hist') adjacent'
      where
        adjacent' = Graph.adjacent k g `Set.difference` maybe Set.empty Set.fromFoldable hist
        hist' = maybe (pure k) (nelCons k) hist

instruments :: forall k v. Ord k => { cause :: k, effect :: k } -> Set k -> Graph k v -> Set k
instruments { cause, effect } conditionedOn g =
  dConnectedTo cause conditionedOn g `Set.intersection`
  dSeparatedFrom effect conditionedOn (intervene cause g)

isInstrument ::
  forall k v. Ord k => k -> { cause :: k, effect :: k } -> Set k -> Graph k v -> Boolean
isInstrument i ks conditionedOn g =
  i `Set.member` instruments ks conditionedOn g

intervene :: forall k v. Ord k => k -> Graph k v -> Graph k v
intervene k g = foldr removePointers g <<< Map.keys <<< Graph.toMap $ g
  where
    removePointers = Graph.alterEdges (map $ Set.filter (_ /= k))

-- Returns `Nothing` iff the conditioning set contains the cause or the effect
satisfyBackdoor ::
  forall k v.
  Ord k =>
  { cause :: k, effect :: k } -> Set k -> Graph k v -> Maybe Boolean
satisfyBackdoor { cause, effect } conditionedOn g =
  if cause `Set.member` conditionedOn || effect `Set.member` conditionedOn
  then Nothing
  else Just result
  where
    result =
      Foldable.all (not <<< descendsFromCause) conditionedOn &&
      Foldable.all pathBlocked pathsPointingToCause
    pathBlocked = not <<< Set.isEmpty <<< Set.intersection conditionedOn <<< Set.fromFoldable
    descendsFromCause p = cause `Set.member` Graph.descendants p g
    pathsPointingToCause =
      Set.filter ((==) cause <<< NEL.last) $
      allUndirectedPaths (MkTwoSet cause effect) g
