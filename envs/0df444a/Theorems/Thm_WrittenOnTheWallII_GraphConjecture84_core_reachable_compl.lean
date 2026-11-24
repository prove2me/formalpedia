-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_core_reachable_compl
-- name    : WrittenOnTheWallII.GraphConjecture84.core_reachable_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:25:22.406174+00:00
-- url     : https://prove2.me/theorems/cd434fc1-9e4f-49e7-af94-809a0e32b6aa
-- title:
--   Graph Conjecture84: core reachable compl
-- statement:
--   Two core vertices different from a prescribed vertex remain reachable in its
--   ambient deletion graph.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1383-L1393
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1383-L1393

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

theorem WrittenOnTheWallII.GraphConjecture84.core_reachable_compl {G : SimpleGraph α} (K : Finset α)
    (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (c : α) {u v : α} (hu : u ∈ K) (hv : v ∈ K) (huc : u ≠ c) (hvc : v ≠ c) :
    (G.induce ({c}ᶜ : Set α)).Reachable ⟨u, by simpa using huc⟩
      ⟨v, by simpa using hvc⟩ := by sorry
