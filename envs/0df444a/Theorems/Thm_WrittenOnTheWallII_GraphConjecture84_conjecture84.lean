-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_conjecture84
-- name    : WrittenOnTheWallII.GraphConjecture84.conjecture84
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:36:52.243672+00:00
-- url     : https://prove2.me/theorems/112b2023-7b88-42da-912e-1f621fe190f8
-- title:
--   Graph Conjecture84: conjecture84
-- statement:
--   **WOWII Conjecture 84.** For a finite simple connected graph `G` with positive minimum
--   degree, `tree(G) ≥ 2 · rad(G) / δ(G)`.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Solution.lean#L24-L27
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Solution.lean#L24-L27

module
public import Definitions.Def_Wowii84_Main
public import Definitions.Def_Wowii84_Solution
set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

theorem WrittenOnTheWallII.GraphConjecture84.conjecture84 (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) (hδ : 0 < G.minDegree) :
    2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) ≤ (largestInducedTreeSize G : ℝ) := by sorry
