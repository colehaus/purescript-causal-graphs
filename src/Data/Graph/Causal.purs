module Data.Graph.Causal where

import Prelude

import Causal.Kernel (AreDisjoint, IsPathOf, Path(..), PathOf, allUndirectedPaths, cause, cause_disjoint, disjointnessCauseEffect, disjointnessTwoSet, effect, effect_disjoint, pathOf_isPathOf)
import Data.Either (Either(..), isLeft, isRight)
import Data.Foldable (foldr)
import Data.Foldable as Foldable
import Data.Function (on)
import Data.Graph (Graph)
import Data.Graph as Graph
import Data.Graph.Causal.Utility (after, before, distinctTwoSets, powerSet)
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.TwoSet (TwoSet(..))
import GDP.Named (Named, name, name2, name3, unName)
import GDP.Proof (Proof, axiom)

data IsCollider collider path graph

isCollider ::
  forall p g k v.
  Ord k =>
  Proof (IsPathOf p g) ->
  k -> Named p (Path k) -> Named g (Graph k v) ->
  Maybe (Proof (IsCollider k p g))
isCollider _ k path graph =
  if test then Just axiom else Nothing
  where
    test =
      Foldable.any (\a -> Graph.isParentOf (unName graph) a k) (after k (unName path)) &&
      Foldable.any (\b -> Graph.isParentOf (unName graph) b k) (before k (unName path))

data AreDConnected vertices conditionedOn graph

areDConnected ::
  forall n m g k v.
  Ord k =>
  Proof (AreDisjoint n m) ->
  Named n (TwoSet k) -> Named m (Set k) -> Named g (Graph k v) ->
  Maybe (Proof (AreDConnected n m g))
areDConnected p ks conditionedOn g =
  if test then Just axiom else Nothing
  where
    test = not <<< Set.isEmpty $ dConnectedBy p ks conditionedOn g

dConnectedBy ::
  forall n m g k v.
  Ord k =>
  Proof (AreDisjoint n m) ->
  Named n (TwoSet k) -> Named m (Set k) -> Named g (Graph k v) ->
  Set (Named (PathOf g) (Path k))
dConnectedBy _ ks conditionedOn g =
  Set.filter (\p -> isLeft $ blocked (pathOf_isPathOf p) p conditionedOn g) $
  allUndirectedPaths (unName ks) g

data Blocked path conditionedOn graph
data Unblocked path conditionedOn graph

blocked ::
  forall g k m p v. Ord k =>
  Proof (IsPathOf p g) ->
  Named p (Path k) -> Named m (Set k) -> Named g (Graph k v) ->
  Either (Proof (Unblocked p m g)) (Proof (Blocked p m g)) 
blocked p path conditionedOn g =
  if nonCollidersDisjointFromW && collidersAncestorsOfW
  then Left axiom
  else Right axiom
  where
    { yes, no } =
      List.partition
        (\k -> isJust $ isCollider p k path g) <<< List.fromFoldable $
        unName path
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
        maybe false (\p -> isJust $ areDConnected p kv conditionedOn g') $
        disjointnessTwoSet kv conditionedOn)

data AreDSeparated vertices conditionedOn graph

areDSeparated ::
  forall n m g k v.
  Ord k =>
  Proof (AreDisjoint n m) ->
  Named n (TwoSet k) -> Named m (Set k) -> Named g (Graph k v) ->
  Maybe (Proof (AreDSeparated n m g))
areDSeparated p ks conditionedOn g =
  if test then Just axiom else Nothing
  where
    test = Set.isEmpty $ dConnectedBy p ks conditionedOn g

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
         maybe false (\p -> isJust $ areDSeparated p kv conditionedOn g') $
         disjointnessTwoSet kv conditionedOn)

dSeparations :: forall k v. Ord k => Set k -> Graph k v -> Set (TwoSet k)
dSeparations conditionedOn' g =
  Set.filter areDSeparated' <<<
  distinctTwoSets <<<
  Map.keys <<< Graph.toMap $ g
  where
    areDSeparated' ks' =
      name3 ks' conditionedOn' g (\ks conditionedOn g' ->
        maybe false (\p -> isJust $ areDSeparated p ks conditionedOn g') $
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

data IsInstrument instrument causeEffect conditionedOn graph

isInstrument ::
  forall i n m g k v.
  Ord k =>
  Proof (AreDisjoint n m) ->
  Named i k -> Named n { cause :: k, effect :: k } -> Named m (Set k) -> Named g (Graph k v) ->
  Maybe (Proof (IsInstrument i n m g))
isInstrument p i ks conditionedOn g =
  if test then Just axiom else Nothing
  where
    test = Set.member (unName i) $ instruments p ks conditionedOn (unName g)

intervene :: forall k v. Ord k => k -> Graph k v -> Graph k v
intervene k g = foldr removePointers g <<< Map.keys <<< Graph.toMap $ g
  where
    removePointers = Graph.alterEdges (map $ Set.filter (_ /= k))

data IsBackdoor causeEffect conditionedOn graph

isBackdoor ::
  forall n m g k v.
  Ord k =>
  Proof (AreDisjoint n m) ->
  Named n { cause :: k, effect :: k } -> Named m (Set k) -> Named g (Graph k v) ->
  Maybe (Proof (IsBackdoor n m g))
isBackdoor _ causeEffect conditionedOn g =
  if test then Just axiom else Nothing
  where
    { cause, effect } = unName causeEffect
    test =
      Set.isEmpty (Graph.descendants cause (unName g) `Set.intersection` unName conditionedOn) &&
      Foldable.all (\p -> isRight $ blocked (pathOf_isPathOf p) p conditionedOn g) pathsPointingToCause
    pathsPointingToCause =
      Set.filter (pointsAtHead <<< unName) $
      allUndirectedPaths (MkTwoSet cause effect) g
      where
        pointsAtHead (MkPath head xs last) =
          maybe false (Set.member head) <<< Graph.outEdges second $ unName g
          where
            second = fromMaybe last <<< List.head $ xs

minimalBackdoors ::
  forall k v. Ord k => { cause :: k, effect :: k } -> Graph k v -> Set (Set k)
minimalBackdoors causeEffect = keepSmallest <<< backdoors causeEffect
  where
    keepSmallest xs = Set.filter (\s -> m == Set.size s) xs
      where
        -- 0 doesn't really matter since if the set is empty, the filter above will be a no-op
        m = maybe 0 Set.size <<< Foldable.minimumBy (compare `on` Set.size) $ xs

backdoors :: forall k v. Ord k => { cause :: k, effect :: k } -> Graph k v -> Set (Set k)
backdoors { cause, effect } g = name2 g { cause, effect } go
  where
    go :: forall g n. Named g (Graph k v) -> Named n { cause :: k, effect :: k } -> Set (Set k)
    go g' causeEffect =
      Set.filter (\s -> name s checkBackdoor) <<< powerSet <<<
      Set.filter (not <<< flip (Graph.isDescendantOf g) cause) <<<
      Set.delete cause <<< Set.delete effect <<<
      Map.keys <<< Graph.toMap $ g
      where
        checkBackdoor :: forall m. Named m (Set k) -> Boolean
        checkBackdoor conditionedOn =
          case disjointnessCauseEffect causeEffect conditionedOn of
            Just p -> isJust $ isBackdoor p causeEffect conditionedOn g'
            -- This case should never apply because
            -- we delete `cause` and `effect` elsewhere
            Nothing -> false
