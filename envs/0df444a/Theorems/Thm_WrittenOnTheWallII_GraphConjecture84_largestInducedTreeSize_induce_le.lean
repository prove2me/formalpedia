-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_largestInducedTreeSize_induce_le
-- name    : WrittenOnTheWallII.GraphConjecture84.largestInducedTreeSize_induce_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:23:33.272412+00:00
-- url     : https://prove2.me/theorems/da6e3bce-24f6-4108-bd84-53c8e0e49266
-- title:
--   Graph Conjecture84: largest Induced Tree Size induce le
-- statement:
--   Passing to an induced subgraph can only decrease the largest induced-tree order.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L87-L90
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L87-L90

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem WrittenOnTheWallII.GraphConjecture84.largestInducedTreeSize_induce_le (G : SimpleGraph α) (S : Set α)
    [DecidablePred (· ∈ S)] :
    largestInducedTreeSize (G.induce S) ≤ largestInducedTreeSize G := by sorry
