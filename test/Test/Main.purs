module Test.Main where

import Prelude

import Data.Graph as Graph
import Data.Graph.Causal as Causal
import Data.List as List
import Data.Map as Map
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (run)

main :: Effect Unit
main = run [consoleReporter] do
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
  describe "intervene" do
    it "works for examples" do
      let intervened =
            Graph.fromMap (
              Map.fromFoldable
                [ n 'W' [ 'Z' ]
                , n 'X' [ ]
                , n 'Y' [ 'Z' ]
                , n 'Z' [ ]
                ])
      Graph.toMap (Causal.intervene 'Y' graph3) `shouldEqual` Graph.toMap intervened
  describe "dConnectedBy" do
    it "worksForExamples" do
      Causal.dConnectedBy 'X' 'Y' Set.empty graph1 `shouldEqual` Set.empty
      Causal.dConnectedBy 'X' 'Y' (Set.fromFoldable [ 'S' , 'T' ]) graph1 `shouldEqual`
        Set.singleton (List.fromFoldable [ 'X', 'U', 'V', 'W', 'Y' ])
      Causal.dConnectedBy 'X' 'Y' (Set.fromFoldable [ 'S', 'T', 'V']) graph1 `shouldEqual` Set.empty

      Causal.dConnectedBy 'X' 'Z' Set.empty graph2 `shouldEqual` Set.empty
      Causal.dConnectedBy 'X' 'Z' (Set.singleton 'Y') graph2 `shouldEqual` Set.singleton (List.fromFoldable [ 'X', 'Y', 'Z' ])
  describe "instruments" do
    it "worksForExamples" do
      Causal.instruments 'Y' 'Z' Set.empty graph3 `shouldEqual` Set.singleton 'X'
