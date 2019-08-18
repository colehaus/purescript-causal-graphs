module Data.Graph.Causal where

import Prelude

import Causal.Kernel (AreDisjoint, IsPathOf, PathOf, allUndirectedPaths, cause, cause_disjoint, disjointnessTwoSet, effect, effect_disjoint, pathOf_isPathOf)
import Data.Foldable (foldr)
import Data.Foldable as Foldable
import Data.Graph (Graph)
import Data.Graph as Graph
import Data.Graph.Causal.Utility (after, before, distinctTwoSets)
import Data.List.NonEmpty (NonEmptyList)
import Data.List.NonEmpty as NEL
import Data.Map as Map
import Data.Maybe (maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.TwoSet (TwoSet(..))
import GDP.Named (Named, name2, name3, unName)
import GDP.Proof (Proof)

collider ::
  forall p g k v.
  Ord k =>
  Proof (IsPathOf p g) -> k -> Named p (NonEmptyList k) -> Named g (Graph k v) -> Boolean
collider _ k path graph =
  Foldable.any (\a -> Graph.isParentOf (unName graph) a k) (after k (unName path)) &&
  Foldable.any (\b -> Graph.isParentOf (unName graph) b k) (before k (unName path))

areDConnected ::
  forall n m g k v. Ord k =>
  Proof (AreDisjoint n m) ->
  Named n (TwoSet k) -> Named m (Set k) -> Named g (Graph k v) -> Boolean
areDConnected p ks conditionedOn g = not <<< Set.isEmpty $ dConnectedBy p ks conditionedOn g

dConnectedBy ::
  forall n m g k v.
  Ord k =>
  Proof (AreDisjoint n m) ->
  Named n (TwoSet k) -> Named m (Set k) -> Named g (Graph k v) ->
  Set (Named (PathOf g) (NonEmptyList k))
dConnectedBy _ ks conditionedOn g =
  Set.filter unblocked $ allUndirectedPaths (unName ks) g
  where
    unblocked path = nonCollidersDisjointFromW && collidersAncestorsOfW
      where
        { yes, no } = NEL.partition (\k -> collider (pathOf_isPathOf path) k path g) (unName path)
        nonCollidersDisjointFromW =
          Set.isEmpty (Set.fromFoldable no `Set.intersection` unName conditionedOn)
        collidersAncestorsOfW =
          Foldable.all
            (\k -> not <<< Set.isEmpty $
              Set.insert k (Graph.descendants k (unName g)) `Set.intersection` 
              unName conditionedOn)
            yes

dConnectedTo :: 
  forall n m k v.
  Ord k =>
  Proof (AreDisjoint n m) -> Named n k -> Named m (Set k) -> Graph k v -> Set k
dConnectedTo _ k conditionedOn g =
  Set.filter isDConnectedToK <<<
  Set.delete (unName k) <<< Map.keys <<< Graph.toMap $ g
  where
    isDConnectedToK v =
      name2 (MkTwoSet (unName k) v) g (\kv g' ->
        maybe false (\p -> areDConnected p kv conditionedOn g') $
        disjointnessTwoSet kv conditionedOn)

areDSeparated ::
  forall n m g k v.
  Ord k =>
  Proof (AreDisjoint n m) ->
  Named n (TwoSet k) -> Named m (Set k) -> Named g (Graph k v) -> Boolean
areDSeparated p ks conditionedOn g =
  Set.isEmpty $ dConnectedBy p ks conditionedOn g

dSeparatedFrom ::
  forall n m k v.
  Ord k =>
  Proof (AreDisjoint n m) -> Named n k -> Named m (Set k) -> Graph k v -> Set k
dSeparatedFrom _ k conditionedOn g =
   Set.filter isDSeparatedFromK <<<
   Set.delete (unName k) <<< Map.keys <<< Graph.toMap $ g
   where
     isDSeparatedFromK v =
       name2 (MkTwoSet (unName k) v) g (\kv g' ->
         maybe false (\p -> areDSeparated p kv conditionedOn g') $
         disjointnessTwoSet kv conditionedOn)

dSeparations :: forall k v. Ord k => Set k -> Graph k v -> Set (TwoSet k)
dSeparations conditionedOn' g =
  Set.filter areDSeparated' <<<
  distinctTwoSets <<<
  Map.keys <<< Graph.toMap $ g
  where
    areDSeparated' ks' =
      name3 ks' conditionedOn' g (\ks conditionedOn g' ->
        maybe false (\p -> areDSeparated p ks conditionedOn g') $
        disjointnessTwoSet ks conditionedOn)

instruments ::
  forall n m k v.
  Ord k =>
  Proof (AreDisjoint n m) ->
  Named n { cause :: k, effect :: k } -> Named m (Set k) -> Graph k v -> Set k
instruments p causeEffect conditionedOn g =
  connected `Set.intersection` separated
  where
    separated = 
      dSeparatedFrom
        (effect_disjoint p)
        (effect causeEffect)
        conditionedOn
        (intervene (_.cause <<< unName $ causeEffect) g)
    connected =
      dConnectedTo (cause_disjoint p) (cause causeEffect) conditionedOn g

isInstrument ::
  forall n m k v.
  Ord k =>
  Proof (AreDisjoint n m) ->
  k -> Named n { cause :: k, effect :: k } -> Named m (Set k) -> Graph k v -> Boolean
isInstrument p i ks conditionedOn g =
  Set.member i $ instruments p ks conditionedOn g

intervene :: forall k v. Ord k => k -> Graph k v -> Graph k v
intervene k g = foldr removePointers g <<< Map.keys <<< Graph.toMap $ g
  where
    removePointers = Graph.alterEdges (map $ Set.filter (_ /= k))

satisfyBackdoor ::
  forall n m g k v.
  Ord k =>
  Proof (AreDisjoint n m) ->
  Named n { cause :: k, effect :: k } -> Named m (Set k) -> Named g (Graph k v) -> Boolean
satisfyBackdoor _ causeEffect conditionedOn g =
  Foldable.all (not <<< descendsFromCause) (unName conditionedOn) &&
  Foldable.all pathBlocked pathsPointingToCause
  where
    { cause, effect } = unName causeEffect
    pathBlocked = 
      not <<< Set.isEmpty <<< Set.intersection (unName conditionedOn) <<< 
      Set.fromFoldable <<< unName
    descendsFromCause p = cause `Set.member` Graph.descendants p (unName g)
    pathsPointingToCause =
      Set.filter ((==) cause <<< NEL.last <<< unName) $
      allUndirectedPaths (MkTwoSet cause effect) g
