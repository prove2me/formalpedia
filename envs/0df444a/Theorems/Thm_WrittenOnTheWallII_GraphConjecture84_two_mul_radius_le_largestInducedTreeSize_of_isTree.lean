-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_two_mul_radius_le_largestInducedTreeSize_of_isTree
-- name    : WrittenOnTheWallII.GraphConjecture84.two_mul_radius_le_largestInducedTreeSize_of_isTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:24:34.168778+00:00
-- url     : https://prove2.me/theorems/cf632ba6-9671-4076-bd50-a71a1e2f2130
-- title:
--   Graph Conjecture84: two mul radius le largest Induced Tree Size of is Tree
-- statement:
--   Trees satisfy the required twice-radius bound, including the one-vertex tree.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L251-L254
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L251-L254

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

theorem WrittenOnTheWallII.GraphConjecture84.two_mul_radius_le_largestInducedTreeSize_of_isTree {G : SimpleGraph α}
    (hG : G.IsTree) : 2 * G.radius.toNat ≤ largestInducedTreeSize G := by sorry
