-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_exists_pendant_geodesic_family
-- name    : WrittenOnTheWallII.GraphConjecture84.exists_pendant_geodesic_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:30:17.393305+00:00
-- url     : https://prove2.me/theorems/79564ad8-41d5-4099-91f2-ec0d7fe7ecee
-- title:
--   Graph Conjecture84: exists pendant geodesic family
-- statement:
--   The two-side reduction and unique attachment property give a covering family
--   of pendant geodesics rooted in the core, including zero-length paths.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1449-L1519
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1449-L1519

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

theorem WrittenOnTheWallII.GraphConjecture84.exists_pendant_geodesic_family {G : SimpleGraph α} (hG : G.Connected)
    (K : Finset α) (hcard : 3 ≤ K.card) (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (huniq : ∀ (z w : ↥((K : Set α)ᶜ)),
      (G.induce (K : Set α)ᶜ).Reachable z w →
      ∀ {a b : α}, a ∈ K → b ∈ K → G.Adj a z → G.Adj b w → a = b)
    (htwo : ∀ c, ¬ (G.induce ({c}ᶜ : Set α)).Connected →
      ∃ a b : ↥({c}ᶜ : Set α), ∃ q : G.Walk c (b : α),
        q.length = G.dist c b ∧
        ¬ (G.induce ({c}ᶜ : Set α)).Reachable a b ∧
        G.dist c b + 2 ≤ G.dist c a ∧
        ∀ z, z ∈ cutSide G c a ∨ z ∈ q.support) :
    Nonempty (PendantGeodesics G K) := by sorry
