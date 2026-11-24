-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_two_mul_radius_le_largestInducedTreeSize_of_cut_vertex
-- name    : WrittenOnTheWallII.GraphConjecture84.two_mul_radius_le_largestInducedTreeSize_of_cut_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:32:04.240814+00:00
-- url     : https://prove2.me/theorems/ae171b2b-c44a-40c3-9f48-a0a9c5d297ab
-- title:
--   Graph Conjecture84: two mul radius le largest Induced Tree Size of cut vertex
-- statement:
--   The cut-vertex bound, by induction on graph order.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1953-L2035
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1953-L2035

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

theorem WrittenOnTheWallII.GraphConjecture84.two_mul_radius_le_largestInducedTreeSize_of_cut_vertex {G : SimpleGraph α}
    (hG : G.Connected) (hcut : ∃ x, ¬ (G.induce ({x}ᶜ : Set α)).Connected) :
    2 * G.radius.toNat ≤ largestInducedTreeSize G := by sorry
