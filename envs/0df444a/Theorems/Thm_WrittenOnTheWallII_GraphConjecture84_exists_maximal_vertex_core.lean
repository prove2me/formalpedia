-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_exists_maximal_vertex_core
-- name    : WrittenOnTheWallII.GraphConjecture84.exists_maximal_vertex_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:29:38.777827+00:00
-- url     : https://prove2.me/theorems/8ca30ec7-b8f7-4bdc-a4be-1cd814704efd
-- title:
--   Graph Conjecture84: exists maximal vertex core
-- statement:
--   A cyclic graph contains an induced vertex-connected core maximal under vertex inclusion.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1016-L1048
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1016-L1048

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

theorem WrittenOnTheWallII.GraphConjecture84.exists_maximal_vertex_core {G : SimpleGraph α} (hcyc : ¬ G.IsAcyclic) :
    ∃ s : Finset α, 3 ≤ s.card ∧ (G.induce (s : Set α)).Connected ∧
      (∀ x : ↥(s : Set α),
        ((G.induce (s : Set α)).induce ({x}ᶜ : Set ↥(s : Set α))).Connected) ∧
      ∀ t : Finset α, s ⊆ t → 3 ≤ t.card → (G.induce (t : Set α)).Connected →
        (∀ x : ↥(t : Set α),
          ((G.induce (t : Set α)).induce ({x}ᶜ : Set ↥(t : Set α))).Connected) → t = s := by sorry
