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
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..))
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

-- Returns `Nothing` iff the `TwoSet` overlaps with the set conditioned on
areDConnected :: forall k v. Ord k => TwoSet k -> Set k -> Graph k v -> Maybe Boolean
areDConnected ks conditionedOn g = not <<< Set.isEmpty <$> dConnectedBy ks conditionedOn g

-- Returns `Nothing` iff the `TwoSet` overlaps with the set conditioned on
dConnectedBy ::
  forall k v.
  Ord k =>
  TwoSet k -> Set k -> Graph k v -> Maybe (Set (NonEmptyList k))
dConnectedBy ks@(MkTwoSet k1 k2) conditionedOn g =
  if k1 `Set.member` conditionedOn || k2 `Set.member` conditionedOn
  then Nothing
  else Just result
  where
    result = Set.filter unblocked $ allUndirectedPaths ks g
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

-- Returns `Nothing` iff the `k` is in the set conditioned on
dConnectedTo :: forall k v. Ord k => k -> Set k -> Graph k v -> Maybe (Set k)
dConnectedTo k conditionedOn g =
  if k `Set.member` conditionedOn
  then Nothing
  else Just result
  where
    result =
      Set.filter (\v -> fromMaybe false $ areDConnected (MkTwoSet k v) conditionedOn g) <<<
      Set.delete k <<< Map.keys <<< Graph.toMap $ g

areDSeparated :: forall k v. Ord k => TwoSet k -> Set k -> Graph k v -> Maybe Boolean
areDSeparated ks conditionedOn g = Set.isEmpty <$> dConnectedBy ks conditionedOn g

-- Returns `Nothing` iff the `k` is in the set conditioned on
dSeparatedFrom :: forall k v. Ord k => k -> Set k -> Graph k v -> Maybe (Set k)
dSeparatedFrom k conditionedOn g =
  if k `Set.member` conditionedOn
  then Nothing
  else Just result
  where
    result =
      Set.filter (\v -> fromMaybe false $ areDSeparated (MkTwoSet k v) conditionedOn g) <<<
      Set.delete k <<< Map.keys <<< Graph.toMap $ g

dSeparations :: forall k v. Ord k => Set k -> Graph k v -> Set (TwoSet k)
dSeparations conditionedOn g =
  Set.filter (\ks -> fromMaybe false $ areDSeparated ks conditionedOn g) <<<
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

-- Returns `Nothing` iff the cause or the effect is in the set conditioned on
instruments ::
  forall k v.
  Ord k =>
  { cause :: k, effect :: k } -> Set k -> Graph k v -> Maybe (Set k)
instruments { cause, effect } conditionedOn g =
  case
    Tuple
      (dConnectedTo cause conditionedOn g)
      (dSeparatedFrom effect conditionedOn (intervene cause g)) of
    Tuple (Just connected) (Just separated) -> Just $ connected `Set.intersection` separated
    Tuple _ _ -> Nothing

isInstrument ::
  forall k v. Ord k => k -> { cause :: k, effect :: k } -> Set k -> Graph k v -> Maybe Boolean
isInstrument i ks conditionedOn g =
  Set.member i <$> instruments ks conditionedOn g

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
