module Test.Main where

import Prelude

import Data.Array as Array
import Data.Foldable as Foldable
import Data.Function (on)
import Data.Generic.Rep (class Generic)
import Data.Graph (Graph)
import Data.Graph as Graph
import Data.Graph.Causal as Causal
import Data.List as List
import Data.List.NonEmpty as NEL
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (class Newtype, un)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..), uncurry)
import Data.TwoSet (TwoSet(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck as QuickCheck
import Test.QuickCheck.Gen (Gen, suchThat)
import Test.QuickCheck.Gen as Gen
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck')
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (run)

quickCheck'' :: forall t2. QuickCheck.Testable t2 => t2 -> Aff Unit
quickCheck'' = quickCheck' 50

main :: Effect Unit
main = run [consoleReporter] do
  describe "Unit tests" do
    let n k v = Tuple k (Tuple k (Set.fromFoldable v ))
    -- X -> U <- V -> W <- Y <- Z
    --      |         |
    --      v         v
    --      S         T
        graph1 =
          Graph.fromMap (
            Map.fromFoldable
              [ n 'X' [ 'U']
              , n 'U' [ 'S' ]
              , n 'V' [ 'U', 'W' ]
              , n 'W' [ 'T' ]
              , n 'Y' [ 'W' ]
              , n 'Z' [ 'Y' ]
              , n 'S' [ ]
              , n 'T' [ ]
              ])
        -- X -> Y <- Z
        graph2 =
          Graph.fromMap (
            Map.fromFoldable
              [ n 'X' [ 'Y' ]
              , n 'Y' [ ]
              , n 'Z' [ 'Y' ]
              ])
        --        W
        --      /   \
        --      v    v
        -- X -> Y -> Z
        graph3 =
          Graph.fromMap (
            Map.fromFoldable
              [ n 'W' [ 'Y', 'Z' ]
              , n 'X' [ 'Y' ]
              , n 'Y' [ 'Z' ]
              , n 'Z' [ ]
              ])
        -- Z -> W
        -- |    |
        -- v    v
        -- X -> Y
        graph4 =
          Graph.fromMap (
            Map.fromFoldable
              [ n 'Z' [ 'W', 'X' ]
              , n 'X' [ 'Y' ]
              , n 'W' [ 'Y' ]
              , n 'Y' []
              ])
    it "intervene" do
      let intervened =
            Graph.fromMap (
              Map.fromFoldable
                [ n 'W' [ 'Z' ]
                , n 'X' [ ]
                , n 'Y' [ 'Z' ]
                , n 'Z' [ ]
                ])
      Graph.toMap (Causal.intervene 'Y' graph3) `shouldEqual` Graph.toMap intervened
    it "dConnectedBy" do
      let nel x = unsafePartial $ fromJust <<< NEL.fromList <<< List.fromFoldable $ x
      Causal.dConnectedBy (MkTwoSet 'X' 'Y') Set.empty graph1 `shouldEqual` Just Set.empty

      Causal.dConnectedBy
          (MkTwoSet 'X' 'Y')
          (Set.fromFoldable [ 'S' , 'T' ])
          graph1
        `shouldEqual`
      Just (Set.singleton (nel [ 'X', 'U', 'V', 'W', 'Y' ]))

      Causal.dConnectedBy
          (MkTwoSet 'X' 'Y')
          (Set.fromFoldable [ 'S', 'T', 'V'])
          graph1
        `shouldEqual`
      Just Set.empty

      Causal.dConnectedBy (MkTwoSet 'X' 'Z') Set.empty graph2 `shouldEqual` Just Set.empty

      Causal.dConnectedBy (MkTwoSet 'X' 'Z') (Set.singleton 'Y') graph2 `shouldEqual`
        Just (Set.singleton (nel [ 'X', 'Y', 'Z' ]))

      Causal.dConnectedBy (MkTwoSet 'W' 'Z') Set.empty graph3 `shouldEqual`
        Just (Set.fromFoldable
          [
            nel [ 'W', 'Z' ]
          , nel [ 'W', 'Y', 'Z' ]
          ])
    it "dSeparations" do
      Causal.dSeparations (Set.singleton 'X') graph2 `shouldEqual` Set.empty
      Causal.dSeparations (Set.singleton 'Y') graph2 `shouldEqual` Set.empty
      Causal.dSeparations (Set.singleton 'Z') graph2 `shouldEqual` Set.empty
      Causal.dSeparations Set.empty graph1
        `shouldEqual`
      Set.fromFoldable
        [ MkTwoSet 'X' 'T'
        , MkTwoSet 'X' 'V'
        , MkTwoSet 'X' 'W'
        , MkTwoSet 'Y' 'S'
        , MkTwoSet 'Y' 'U'
        , MkTwoSet 'Y' 'V'
        , MkTwoSet 'Y' 'X'
        , MkTwoSet 'Z' 'S'
        , MkTwoSet 'Z' 'U'
        , MkTwoSet 'Z' 'V'
        , MkTwoSet 'Z' 'X'
        ]
      Causal.dSeparations (Set.singleton 'U') graph1
        `shouldEqual`
      Set.fromFoldable
        [ MkTwoSet 'T' 'S'
        , MkTwoSet 'V' 'S'
        , MkTwoSet 'W' 'S'
        , MkTwoSet 'X' 'S'
        , MkTwoSet 'Y' 'S'
        , MkTwoSet 'Y' 'V'
        , MkTwoSet 'Y' 'X'
        , MkTwoSet 'Z' 'S'
        , MkTwoSet 'Z' 'V'
        , MkTwoSet 'Z' 'X'
        ]
    it "instruments" do
      Causal.instruments { cause: 'Y', effect: 'Z' } Set.empty graph3 `shouldEqual`
        Just (Set.singleton 'X')
    it "backdoor" do
      Causal.satisfyBackdoor { cause: 'X', effect: 'Y' } (Set.singleton 'W') graph4
        `shouldEqual`
      Just true
  describe "Relationships" do
    it "dSeparatedFrom and dConnectedTo cohere" do
      quickCheck'' ado
        k <- arbitrary
        conditionOn <- genSet arbitrary
        g <- genAcyclicGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
        in
          let
            mConnections = Causal.dConnectedTo k conditionOn g
            mSeparations = Causal.dSeparatedFrom k conditionOn g
            keys = Map.keys (Graph.toMap g)
          in
            case Tuple mConnections mSeparations of
              Tuple Nothing Nothing -> true
              Tuple (Just connections) (Just separations) ->
                Set.fromFoldable
                  [ connections
                  , separations
                  , keys `Set.intersection` conditionOn
                  , keys `Set.intersection` Set.singleton k
                  ]
                `isPartitionOf`
                  keys
              Tuple _ _ -> unsafeCrashWith "Should never happen"

isPartitionOf :: forall a. Ord a => Set (Set a) -> Set a -> Boolean
isPartitionOf ss s =
  Set.unions ss == s && Foldable.all (Set.isEmpty <<< uncurry Set.intersection) (pairs ss)

pairs :: forall a. Eq a => Set a -> Array (Tuple a a)
pairs ss = Array.filter (uncurry (/=)) ado
  s1 <- ss'
  s2 <- ss'
  in Tuple s1 s2
  where
    ss' = Array.fromFoldable ss

genAcyclicGraph :: forall k v. Ord k => Gen k -> Gen v -> Gen (Graph k v)
genAcyclicGraph genK genV = suchThat (genGraph genK genV) Graph.isAcyclic

genGraph :: forall k v. Ord k => Gen k -> Gen v -> Gen (Graph k v)
genGraph genK genV = ado
  l <- Gen.arrayOf genElement
  in Graph.fromMap <<< Map.fromFoldable $ l
    where
      genElement :: Gen (Tuple k (Tuple v (Set k)))
      genElement = ado
        k <- genK
        v <- genV
        ks <- genSet genK
        in (Tuple k (Tuple v ks))

genSet :: forall a. Ord a => Gen a -> Gen (Set a)
genSet genA = Set.fromFoldable <$> Gen.arrayOf genA

-- Convenient for use with specs
newtype GraphWrapper k v = G (Graph k v)
derive instance newtypeStringGraph :: Newtype (GraphWrapper k v) _
instance eqStringGraph :: (Eq k, Eq v) => Eq (GraphWrapper k v) where
  eq = eq `on` (Graph.toMap <<< un G)
instance showStringGraph :: (Show k, Show v) => Show (GraphWrapper k v) where
  show = show <<< Graph.toMap <<< un G

-- We want to make the graph denser so that we actually have edges and cycles
newtype SmallInt = MkSmallInt Int
derive instance eqSmallInt :: Eq SmallInt
derive instance ordSmallInt :: Ord SmallInt
derive instance genericSmallInt :: Generic SmallInt _
derive instance newtypeSmallInt :: Newtype SmallInt _
derive newtype instance semiringSmallInt :: Semiring SmallInt
derive newtype instance ringSmallInt :: Ring SmallInt
instance showSmallInt :: Show SmallInt where
  show (MkSmallInt i) = show i
instance arbitrarySmallInt :: QuickCheck.Arbitrary SmallInt where
  arbitrary = MkSmallInt <$> Gen.chooseInt 1 20
