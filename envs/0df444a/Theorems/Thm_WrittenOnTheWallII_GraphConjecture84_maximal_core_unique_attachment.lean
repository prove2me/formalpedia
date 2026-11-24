-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_maximal_core_unique_attachment
-- name    : WrittenOnTheWallII.GraphConjecture84.maximal_core_unique_attachment
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:29:50.311506+00:00
-- url     : https://prove2.me/theorems/3bcbdc84-ae5f-47a9-8832-a8a4d4cbf80e
-- title:
--   Graph Conjecture84: maximal core unique attachment
-- statement:
--   Every connected outside region has at most one attachment vertex in a maximal core.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1229-L1269
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1229-L1269

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

theorem WrittenOnTheWallII.GraphConjecture84.maximal_core_unique_attachment {G : SimpleGraph α} (K : Finset α)
    (hcard : 3 ≤ K.card) (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (hmax : ∀ t : Finset α, K ⊆ t → 3 ≤ t.card → (G.induce (t : Set α)).Connected →
      (∀ x : ↥(t : Set α),
        ((G.induce (t : Set α)).induce ({x}ᶜ : Set ↥(t : Set α))).Connected) → t = K)
    (z w : ↥((K : Set α)ᶜ)) (hr : (G.induce (K : Set α)ᶜ).Reachable z w)
    {a b : α} (ha : a ∈ K) (hb : b ∈ K) (haz : G.Adj a z) (hbw : G.Adj b w) : a = b := by sorry
