-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_radius_add_two_le_largestInducedTreeSize_of_leaf
-- name    : WrittenOnTheWallII.GraphConjecture84.radius_add_two_le_largestInducedTreeSize_of_leaf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:28:13.974968+00:00
-- url     : https://prove2.me/theorems/2c9b9e51-1bb2-4b74-90af-e6c113396450
-- title:
--   Graph Conjecture84: radius add two le largest Induced Tree Size of leaf
-- statement:
--   A leaf adds one more vertex to any geodesic starting at its neighbor and avoiding it.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L312-L352
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L312-L352

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

theorem WrittenOnTheWallII.GraphConjecture84.radius_add_two_le_largestInducedTreeSize_of_leaf {G : SimpleGraph α}
    [DecidableRel G.Adj] (hG : G.Connected) {u : α} (hu : G.degree u = 1)
    (hr : 2 ≤ G.radius.toNat) : G.radius.toNat + 2 ≤ largestInducedTreeSize G := by sorry
