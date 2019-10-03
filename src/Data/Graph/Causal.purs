module Data.Graph.Causal where

import Prelude

import Causal.Kernel (AreDisjoint, IsPathOf, Path(..), PathOf, allDirectedPaths, allUndirectedPaths, cause, cause_disjoint, disjointnessCauseEffect, disjointnessTwoSet, effect, effect_disjoint, pathOf_isPathOf)
import Data.Either (Either(..), either, isLeft, isRight)
import Data.Either as Either
import Data.Foldable (foldr)
import Data.Foldable as Foldable
import Data.Function (on)
import Data.Graph (Graph)
import Data.Graph as Graph
import Data.Graph.Causal.Utility (after, before, distinctTwoSets, powerSet)
import Data.List ((:))
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust, maybe)
import Data.NonEmpty (foldl1, (:|))
import Data.Set (Set)
import Data.Set as Set
import Data.TwoSet (TwoSet(..))
import GDP.Named (Named, name, name2, name3, unName)
import GDP.Proof (Proof, axiom)
import Partial.Unsafe (unsafeCrashWith)

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
  Set.filter (\p -> isLeft $ isBlocked (pathOf_isPathOf p) p conditionedOn g) $
  allUndirectedPaths (unName ks) g

data Blocked path conditionedOn graph
data Unblocked path conditionedOn graph

isBlocked ::
  forall g k m p v. Ord k =>
  Proof (IsPathOf p g) ->
  Named p (Path k) -> Named m (Set k) -> Named g (Graph k v) ->
  Either (Proof (Unblocked p m g)) (Proof (Blocked p m g))
isBlocked p path conditionedOn g =
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

data SatisfiesBackdoor causeEffect conditionedOn graph

-- | Returns either a proof witness or a set of the remaining back-door paths
-- | (which could be empty)
satisifiesBackdoor ::
  forall n m g k v.
  Ord k =>
  Proof (AreDisjoint n m) ->
  Named n { cause :: k, effect :: k } -> Named m (Set k) -> Named g (Graph k v) ->
  Either (Set (Named (PathOf g) (Path k))) (Proof (SatisfiesBackdoor n m g))
satisifiesBackdoor _ causeEffect conditionedOn g =
  if test then Right axiom else Left remainingBackdoorPaths
  where
    { cause, effect } = unName causeEffect
    remainingBackdoorPaths =
      Set.filter
        (\p -> isLeft $ isBlocked (pathOf_isPathOf p) p conditionedOn g)
        (backdoorPaths { cause, effect } g)
    test =
      Set.isEmpty (Graph.descendants cause (unName g) `Set.intersection` unName conditionedOn) &&
      Set.isEmpty remainingBackdoorPaths

backdoorPaths ::
  forall g k v.
  Ord k =>
  { cause :: k, effect :: k } -> Named g (Graph k v) -> Set (Named (PathOf g) (Path k))
backdoorPaths { cause, effect } g =
  Set.filter (pointsAtHead <<< unName) $
  allUndirectedPaths (MkTwoSet cause effect) g
  where
    pointsAtHead (MkPath head xs last) =
      maybe false (Set.member head) <<< Graph.outEdges second $ unName g
      where
        second = fromMaybe last <<< List.head $ xs


minimalBackdoors ::
  forall g k v. Ord k =>
  { cause :: k, effect :: k } -> Named g (Graph k v) ->
  Either (Set (Named (PathOf g) (Path k))) (Set (Set k))
minimalBackdoors causeEffect = map keepSmallest <<< backdoorSets causeEffect
  where
    keepSmallest xs = Set.filter (\s -> m == Set.size s) xs
      where
        -- 0 doesn't really matter since if the set is empty, the filter above will be a no-op
        m = maybe 0 Set.size <<< Foldable.minimumBy (compare `on` Set.size) $ xs

-- | Returns either each set of conditioning vertices that satisfies the backdoor criterion or
-- | the backdoor paths which can't be avoided by any set of conditioning vertices
backdoorSets ::
  forall g k v.
  Ord k =>
  { cause :: k, effect :: k } -> Named g (Graph k v) ->
  Either (Set (Named (PathOf g) (Path k))) (Set (Set k))
backdoorSets { cause, effect } g = name { cause, effect } go
  where
    go ::
      forall n.
      Named n { cause :: k, effect :: k } ->
      Either (Set (Named (PathOf g) (Path k))) (Set (Set k))
    go causeEffect =
      anyBackdoorSets <<<
      Set.map (\s -> name s checkBackdoor) <<< powerSet <<<
      -- More pruning for performance
      Set.filter (not <<< flip (Graph.isDescendantOf (unName g)) cause) <<<
      Set.delete cause <<< Set.delete effect $
      backdoorPathVertices
      where
        -- These are the only vertices that could possibly satisfy the backdoor criterion
        -- so we look only at these instead of all vertices as a performance optimization
        backdoorPathVertices =
          Set.unions <<< Set.map (Set.fromFoldable <<< unName) <<<
          backdoorPaths (unName causeEffect) $ g
        anyBackdoorSets backdoorResults =
          if Foldable.any isRight backdoorResults
          then
            Right <<<
            Set.fromFoldable <<< List.catMaybes <<< map Either.hush <<< List.fromFoldable $
            backdoorResults
          -- If blocking one backdoor path opens another and vice versa,
          -- the intersections of unblocked paths might be empty
          else Left <<< intersections <<<
               List.catMaybes <<< map (either Just (const Nothing)) <<<
               List.fromFoldable $ backdoorResults
          where
            intersections = foldl1 Set.intersection <<< nonEmpty
              where
                nonEmpty (x : xs) = x :| xs
                nonEmpty _ =
                  unsafeCrashWith
                    ("`powerSet` always returns at least one element" <>
                    "and if none of the elements are `Right`," <>
                    "there must be at least one left")
        checkBackdoor ::
          forall m.
          Named m (Set k) -> Either (Set (Named (PathOf g) (Path k))) (Set k)
        checkBackdoor conditionedOn =
          case disjointnessCauseEffect causeEffect conditionedOn of
            Just p ->
              const (unName conditionedOn) <$> satisifiesBackdoor p causeEffect conditionedOn g
            Nothing ->
              unsafeCrashWith "We already deleted cause and effect from the vertices considered"

data SatisfiesFrontdoor causeEffect conditionedOn graph

-- | Returns either a proof witness or a set of the remaining front-door paths
-- | (which could be empty)
satisfiesFrontdoor ::
  forall n m g k v.
  Ord k =>
  Proof (AreDisjoint n m) ->
  Named n { cause :: k, effect :: k } -> Named m (Set k) -> Named g (Graph k v) ->
  Either (Set (Named (PathOf g) (Path k))) (Proof (SatisfiesBackdoor n m g))
satisfiesFrontdoor _ causeEffect conditionedOn g =
  if test then Right axiom else Left remainingFrontdoorPaths
  where
    { cause, effect } = unName causeEffect
    test =
      Set.isEmpty remainingFrontdoorPaths &&
      Foldable.all
        (\p -> name Set.empty (\s -> isRight $ isBlocked (pathOf_isPathOf p) p s g))
        backdoorPathsFromCauseToConditioningSet &&
      Foldable.all
        (\p -> name (Set.singleton cause) (\s -> isRight $ isBlocked (pathOf_isPathOf p) p s g))
        backdoorPathsFromConditioningSetToEffect
    remainingFrontdoorPaths =
      Set.filter
        (\p -> isLeft $ isBlocked (pathOf_isPathOf p) p conditionedOn g)
        (frontdoorPaths (unName causeEffect) g)
    backdoorPathsFromCauseToConditioningSet =
      Set.unions (Set.map (\k -> backdoorPaths { cause, effect: k} g) (unName conditionedOn))
    backdoorPathsFromConditioningSetToEffect =
      Set.unions (Set.map (\k -> backdoorPaths { cause: k, effect} g) (unName conditionedOn))

frontdoorPaths ::
  forall g k v.
  Ord k =>
  { cause :: k, effect :: k } -> Named g (Graph k v) -> Set (Named (PathOf g) (Path k))
frontdoorPaths { cause, effect } = allDirectedPaths { start: cause, end: effect }

-- | Returns either each set of conditioning vertices that satisfies the frontdoor criterion or
-- | the frontdoor paths which can't be avoided by any set of conditioning vertices
frontdoorSets ::
  forall g k v.
  Ord k =>
  { cause :: k, effect :: k } -> Named g (Graph k v) ->
  Either (Set (Named (PathOf g) (Path k))) (Set (Set k))
frontdoorSets { cause, effect } g = name { cause, effect } go
  where
    go ::
      forall n.
      Named n { cause :: k, effect :: k } ->
      Either (Set (Named (PathOf g) (Path k))) (Set (Set k))
    go causeEffect =
      anyFrontdoorSets <<<
      Set.map (\s -> name s checkFrontdoor) <<< powerSet <<<
      -- More pruning for performance
      Set.filter (not <<< flip (Graph.isDescendantOf (unName g)) cause) <<<
      Set.delete cause <<< Set.delete effect $
      frontdoorPathVertices
      where
        -- These are the only vertices that could possibly satisfy the backdoor criterion
        -- so we look only at these instead of all vertices as a performance optimization
        frontdoorPathVertices =
          Set.unions <<< Set.map (Set.fromFoldable <<< unName) <<<
          frontdoorPaths (unName causeEffect) $ g
        anyFrontdoorSets frontdoorResults =
          if Foldable.any isRight frontdoorResults
          then
            Right <<<
            Set.fromFoldable <<< List.catMaybes <<< map Either.hush <<< List.fromFoldable $
            frontdoorResults
          -- If blocking one backdoor path opens another and vice versa,
          -- the intersections of unblocked paths might be empty
          else Left <<< intersections <<<
               List.catMaybes <<< map (either Just (const Nothing)) <<<
               List.fromFoldable $ frontdoorResults
          where
            intersections = foldl1 Set.intersection <<< nonEmpty
              where
                nonEmpty (x : xs) = x :| xs
                nonEmpty _ =
                  unsafeCrashWith
                    ("`powerSet` always returns at least one element" <>
                    "and if none of the elements are `Right`," <>
                    "there must be at least one left")
        checkFrontdoor ::
          forall m.
          Named m (Set k) -> Either (Set (Named (PathOf g) (Path k))) (Set k)
        checkFrontdoor conditionedOn =
          case disjointnessCauseEffect causeEffect conditionedOn of
            Just p ->
              const (unName conditionedOn) <$> satisfiesFrontdoor p causeEffect conditionedOn g
            Nothing ->
              unsafeCrashWith "We already deleted cause and effect from the vertices considered"
