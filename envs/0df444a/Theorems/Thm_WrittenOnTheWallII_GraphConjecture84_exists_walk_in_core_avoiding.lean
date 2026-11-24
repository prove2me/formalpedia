-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_exists_walk_in_core_avoiding
-- name    : WrittenOnTheWallII.GraphConjecture84.exists_walk_in_core_avoiding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:24:09.312029+00:00
-- url     : https://prove2.me/theorems/eeb74fa9-534b-4dd6-be60-50a3276b71d6
-- title:
--   Graph Conjecture84: exists walk in core avoiding
-- statement:
--   Paths within a vertex-connected core can avoid any prescribed vertex.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1068-L1106
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1068-L1106

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

theorem WrittenOnTheWallII.GraphConjecture84.exists_walk_in_core_avoiding {G : SimpleGraph α} (K : Finset α)
    (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (x : α) {u v : α} (hu : u ∈ K) (hv : v ∈ K) (hux : u ≠ x) (hvx : v ≠ x) :
    ∃ p : G.Walk u v, (∀ z ∈ p.support, z ∈ K) ∧ x ∉ p.support := by sorry
