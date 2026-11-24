-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_path_support_subset_maximal_core
-- name    : WrittenOnTheWallII.GraphConjecture84.path_support_subset_maximal_core
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:29:57.927802+00:00
-- url     : https://prove2.me/theorems/79cfa15d-afae-4d27-a1c5-0ec67f5c2f53
-- title:
--   Graph Conjecture84: path support subset maximal core
-- statement:
--   Maximality forces every path between two core vertices to remain in the core.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1202-L1226
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1202-L1226

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

theorem WrittenOnTheWallII.GraphConjecture84.path_support_subset_maximal_core {G : SimpleGraph α} (K : Finset α)
    (hcard : 3 ≤ K.card) (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (hmax : ∀ t : Finset α, K ⊆ t → 3 ≤ t.card → (G.induce (t : Set α)).Connected →
      (∀ x : ↥(t : Set α),
        ((G.induce (t : Set α)).induce ({x}ᶜ : Set ↥(t : Set α))).Connected) → t = K)
    {a b : α} (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b)
    (p : G.Walk a b) (hp : p.IsPath) : ∀ z ∈ p.support, z ∈ K := by sorry
