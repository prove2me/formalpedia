-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_reachable_compl_of_mem_geodesic
-- name    : WrittenOnTheWallII.GraphConjecture84.reachable_compl_of_mem_geodesic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:23:29.16881+00:00
-- url     : https://prove2.me/theorems/354daaf1-3b5d-45df-b0ae-5d1dc7f2ab80
-- title:
--   Graph Conjecture84: reachable compl of mem geodesic
-- statement:
--   After removing the initial vertex of a geodesic, its remaining vertices still reach
--   the endpoint in the deletion graph.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L646-L665
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L646-L665

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

theorem WrittenOnTheWallII.GraphConjecture84.reachable_compl_of_mem_geodesic {G : SimpleGraph α} {c a z : α}
    (p : G.Walk c a) (hp : p.length = G.dist c a) (ha : a ≠ c)
    (hz : z ∈ p.support) (hzc : z ≠ c) :
    (G.induce ({c}ᶜ : Set α)).Reachable
      ⟨z, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzc⟩
      ⟨a, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ha⟩ := by sorry
