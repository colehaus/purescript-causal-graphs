module Causal.Kernel
  ( Cause
  , AreDisjoint
  , Effect
  , IsPathOf
  , PathOf
  , allUndirectedPaths
  , disjointnessCauseEffect
  , disjointnessTwoSet
  , disjointnessSingleton
  , cause
  , cause_disjoint
  , effect
  , effect_disjoint
  , pathOf_isPathOf
  ) where

import Prelude

import Data.Foldable as Foldable
import Data.Graph (Graph)
import Data.Graph as Graph
import Data.List.NonEmpty (NonEmptyList)
import Data.List.NonEmpty as NEL
import Data.List.Types (nelCons)
import Data.Maybe (Maybe(..), maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.TwoSet (TwoSet(..))
import GDP.Named (Defn, Named, defn, unName)
import GDP.Proof (Proof, axiom)

data PathOf g = MkPathOf Defn

allUndirectedPaths ::
  forall g k v.
  Ord k =>
  TwoSet k -> Named g (Graph k v) -> Set (Named (PathOf g) (NonEmptyList k))
allUndirectedPaths (MkTwoSet start end) g =
  Set.map (defn MkPathOf <<< NEL.reverse) $ go Nothing start
  where
    go hist k =
      if end == k
      then Set.singleton hist'
      else
        if adjacent' == Set.empty
        then Set.empty
        else Foldable.foldMap (go $ Just hist') adjacent'
      where
        adjacent' =
          Graph.adjacent k (unName g) `Set.difference` maybe Set.empty Set.fromFoldable hist
        hist' = maybe (pure k) (nelCons k) hist

data IsPathOf p g

pathOf ::
  forall p k g v.
  Ord k =>
  Named p (NonEmptyList k) -> Named g (Graph k v) -> Maybe (Proof (IsPathOf p g))
pathOf p g =
  if Graph.isValidPath (unName g) (unName p)
  then Just axiom
  else Nothing

pathOf_isPathOf :: forall g a. Named (PathOf g) a -> Proof (IsPathOf (PathOf g) g)
pathOf_isPathOf p = axiom

data AreDisjoint x y

disjointnessTwoSet ::
  forall n m a.
  Ord a =>
  Named n (TwoSet a) -> Named m (Set a) -> Maybe (Proof (AreDisjoint n m))
disjointnessTwoSet twoSet set =
  if k1 `Set.member` unName set || k2 `Set.member` unName set
  then Nothing
  else Just axiom
  where
    MkTwoSet k1 k2 = unName twoSet

disjointnessSingleton ::
  forall n m a.
  Ord a =>
  Named n a -> Named m (Set a) -> Maybe (Proof (AreDisjoint n m))
disjointnessSingleton k set =
  if unName k `Set.member` unName set
  then Nothing
  else Just axiom

disjointnessCauseEffect ::
  forall n m a.
  Ord a =>
  Named n { cause :: a, effect :: a } -> Named m (Set a) -> Maybe (Proof (AreDisjoint n m))
disjointnessCauseEffect causeEffect set =
  if cause `Set.member` unName set || effect `Set.member` unName set
  then Nothing
  else Just axiom
  where
    { cause, effect } = unName causeEffect

newtype Cause x = MkCause Defn
newtype Effect x = MkEffect Defn

cause :: forall n a. Named n { cause :: a, effect :: a } -> Named (Cause n) a
cause causeEffect = defn MkCause (_.cause <<< unName $ causeEffect)

effect :: forall n a. Named n { cause :: a, effect :: a } -> Named (Effect n) a
effect causeEffect = defn MkEffect (_.effect <<< unName $ causeEffect)

effect_disjoint :: forall n m. Proof (AreDisjoint n m) -> Proof (AreDisjoint (Effect n) m)
effect_disjoint _ = axiom

cause_disjoint :: forall n m. Proof (AreDisjoint n m) -> Proof (AreDisjoint (Cause n) m)
cause_disjoint _ = axiom

