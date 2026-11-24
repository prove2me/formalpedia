-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_conjecture84_proof
-- name    : WrittenOnTheWallII.GraphConjecture84.conjecture84_proof
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:32:00.324939+00:00
-- url     : https://prove2.me/theorems/8a341893-2c94-4000-8c22-c14896a9a840
-- title:
--   Graph Conjecture84: conjecture84 proof
-- statement:
--   **WOWII Conjecture 84.** For a finite simple connected graph `G` with positive minimum
--   degree, `tree(G) ≥ 2 · rad(G) / δ(G)`.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L2039-L2072
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L2039-L2072

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

theorem WrittenOnTheWallII.GraphConjecture84.conjecture84_proof {β : Type*} [Fintype β] [DecidableEq β] [Nontrivial β]
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (h : G.Connected) (hδ : 0 < G.minDegree) :
    2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) ≤ (largestInducedTreeSize G : ℝ) := by sorry
