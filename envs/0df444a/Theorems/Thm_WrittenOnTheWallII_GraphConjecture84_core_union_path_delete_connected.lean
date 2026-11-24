-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_core_union_path_delete_connected
-- name    : WrittenOnTheWallII.GraphConjecture84.core_union_path_delete_connected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:29:34.88781+00:00
-- url     : https://prove2.me/theorems/459ee64f-0891-438b-b2bc-b96a5cb4f5f0
-- title:
--   Graph Conjecture84: core union path delete connected
-- statement:
--   Adding a path between distinct vertices of a vertex-connected core preserves
--   connectedness after every vertex deletion.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1111-L1199
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1111-L1199

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
set_option maxHeartbeats 800000

theorem WrittenOnTheWallII.GraphConjecture84.core_union_path_delete_connected {G : SimpleGraph α} (K : Finset α)
    (hcard : 3 ≤ K.card) (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    {a b : α} (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b)
    (p : G.Walk a b) (hp : p.IsPath)
    (x : ↥((K ∪ p.support.toFinset : Finset α) : Set α)) :
    ((G.induce ((K ∪ p.support.toFinset : Finset α) : Set α)).induce
      ({x}ᶜ : Set ↥((K ∪ p.support.toFinset : Finset α) : Set α))).Connected := by sorry
