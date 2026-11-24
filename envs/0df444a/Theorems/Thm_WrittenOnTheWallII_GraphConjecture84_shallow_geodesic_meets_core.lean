-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_shallow_geodesic_meets_core
-- name    : WrittenOnTheWallII.GraphConjecture84.shallow_geodesic_meets_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:30:17.926317+00:00
-- url     : https://prove2.me/theorems/15deb662-cbcc-4e3e-9385-757e1212e805
-- title:
--   Graph Conjecture84: shallow geodesic meets core
-- statement:
--   The shallow geodesic at a core cut vertex meets the core only at its root;
--   the rest of the core lies on the other side.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1397-L1431
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1397-L1431

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

theorem WrittenOnTheWallII.GraphConjecture84.shallow_geodesic_meets_core {G : SimpleGraph α} (hG : G.Connected)
    (K : Finset α) (hcard : 3 ≤ K.card) (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (c : α) (hc : c ∈ K) (a b : ↥({c}ᶜ : Set α))
    (q : G.Walk c (b : α)) (hq : q.length = G.dist c b)
    (hsep : ¬ (G.induce ({c}ᶜ : Set α)).Reachable a b)
    (hcover : ∀ z, z ∈ cutSide G c a ∨ z ∈ q.support) :
    (∀ z ∈ K, z ∈ cutSide G c a) ∧ (∀ z ∈ q.support, z ∈ K → z = c) := by sorry
