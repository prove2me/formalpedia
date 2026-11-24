-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_geodesic_branches_bound_of_not_reachable
-- name    : WrittenOnTheWallII.GraphConjecture84.geodesic_branches_bound_of_not_reachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:29:09.277253+00:00
-- url     : https://prove2.me/theorems/8e703253-d99d-4a76-89ba-575fa956cc7f
-- title:
--   Graph Conjecture84: geodesic branches bound of not reachable
-- statement:
--   Geodesics from a cut vertex into different components give the two-branch tree bound.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L668-L689
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L668-L689

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

theorem WrittenOnTheWallII.GraphConjecture84.geodesic_branches_bound_of_not_reachable {G : SimpleGraph α} (hG : G.Connected)
    {c a b : α} (ha : a ≠ c) (hb : b ≠ c)
    (hsep : ¬ (G.induce ({c}ᶜ : Set α)).Reachable
      ⟨a, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ha⟩
      ⟨b, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hb⟩) :
    G.dist c a + G.dist c b + 1 ≤ largestInducedTreeSize G := by sorry
