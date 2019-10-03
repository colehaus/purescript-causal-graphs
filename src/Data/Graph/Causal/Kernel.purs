module Causal.Kernel
  ( Cause
  , AreDisjoint
  , Effect
  , IsPathOf
  , Path(..)
  , PathOf
  , allDirectedPaths
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

import Data.Foldable (class Foldable, foldMap, foldlDefault, foldrDefault)
import Data.Foldable as Foldable
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Graph (Graph)
import Data.Graph as Graph
import Data.List (List(..), (:))
import Data.List as List
import Data.List.NonEmpty (NonEmptyList)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.TwoSet (TwoSet(..))
import GDP.Named (Defn, Named, defn, unName)
import GDP.Proof (Proof, axiom)
import Partial.Unsafe (unsafeCrashWith)

-- List with length at least 2
data Path a = MkPath a (List a) a
derive instance eqPath :: Eq a => Eq (Path a)
derive instance ordPath :: Ord a => Ord (Path a)
derive instance genericPath :: Generic (Path a) _
instance showPath :: Show a => Show (Path a) where
  show = genericShow
instance foldablePath :: Foldable Path where
  foldMap f p = foldMap f (pathToList p)
  foldr x = foldrDefault x
  foldl x = foldlDefault x

pathToList :: forall a. Path a -> List a
pathToList (MkPath head xs last) = List.snoc (head : xs) last

tail :: forall a. Path a -> List a
tail (MkPath head xs last) = List.snoc xs last

reverse :: forall a. Path a -> Path a
reverse p =
  case List.uncons $ List.reverse <<< pathToList $ p of
    Just { head, tail } ->
      case List.unsnoc tail of
        Just { init, last } -> MkPath head init last
        Nothing -> unsafeCrashWith "`reverse` preserves list length"
    _ -> unsafeCrashWith "`reverse` preserves list length"

data PathOf g = MkPathOf Defn

consPath :: forall a. a -> Path a -> Path a
consPath x (MkPath head xs last) = MkPath head (x : xs) last

-- TODO: It seems a little sketchy that all the paths are getting the same name
allUndirectedPaths ::
  forall g k v.
  Ord k =>
  TwoSet k -> Named g (Graph k v) -> Set (Named (PathOf g) (Path k))
allUndirectedPaths (MkTwoSet start end) = bfs Graph.adjacent { start, end }

-- TODO: It seems a little sketchy that all the paths are getting the same name
allDirectedPaths ::
  forall g k v.
  Ord k =>
  { start :: k, end :: k } -> Named g (Graph k v) -> Set (Named (PathOf g) (Path k))
allDirectedPaths = bfs Graph.children

-- TODO: It seems a little sketchy that all the paths are getting the same name
bfs ::
  forall g k v.
  Ord k =>
  (k -> Graph k v -> Set k) -> { start :: k, end :: k } -> Named g (Graph k v) ->
  Set (Named (PathOf g) (Path k))
bfs nextVertices { start,  end } g =
  Set.map (defn MkPathOf <<< reverse) $ go (MkPath end Nil start) start
  where
    go hist k =
      if adjacent' == Set.empty
      then Set.empty
      else Foldable.foldMap goAgain adjacent'
      where
        goAgain x =
          if x == end
          then Set.singleton hist
          else go (consPath x hist) x
        adjacent' =
          nextVertices k (unName g) `Set.difference` Set.fromFoldable (tail hist)

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

