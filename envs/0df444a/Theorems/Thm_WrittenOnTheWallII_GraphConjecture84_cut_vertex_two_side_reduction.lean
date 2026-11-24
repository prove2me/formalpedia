-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_cut_vertex_two_side_reduction
-- name    : WrittenOnTheWallII.GraphConjecture84.cut_vertex_two_side_reduction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:29:25.064549+00:00
-- url     : https://prove2.me/theorems/269cf029-aff6-446d-abb5-422fa764304d
-- title:
--   Graph Conjecture84: cut vertex two side reduction
-- statement:
--   In a minimal counterexample, every cut vertex has one whole side and a shallower
--   geodesic as its other side.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L861-L944
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L861-L944

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

theorem WrittenOnTheWallII.GraphConjecture84.cut_vertex_two_side_reduction {G : SimpleGraph α} (hG : G.Connected)
    (hr : 2 ≤ G.radius.toNat) (hlt : largestInducedTreeSize G < 2 * G.radius.toNat)
    (hsmall : ∀ (S : Set α) [DecidablePred (· ∈ S)], S ≠ Set.univ →
      (G.induce S).Connected →
      (∃ x, ¬ ((G.induce S).induce ({x}ᶜ : Set S)).Connected) →
      2 * (G.induce S).radius.toNat ≤ largestInducedTreeSize (G.induce S))
    (c : α) (hc : ¬ (G.induce ({c}ᶜ : Set α)).Connected) :
    ∃ a b : ↥({c}ᶜ : Set α), ∃ q : G.Walk c (b : α),
      q.length = G.dist c b ∧
      ¬ (G.induce ({c}ᶜ : Set α)).Reachable a b ∧
      G.dist c b + 2 ≤ G.dist c a ∧
      ∀ z : α, z ∈ cutSide G c a ∨ z ∈ q.support := by sorry
