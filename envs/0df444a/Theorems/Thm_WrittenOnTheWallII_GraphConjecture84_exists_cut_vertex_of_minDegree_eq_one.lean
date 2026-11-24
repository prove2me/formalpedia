-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_exists_cut_vertex_of_minDegree_eq_one
-- name    : WrittenOnTheWallII.GraphConjecture84.exists_cut_vertex_of_minDegree_eq_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:27:25.28479+00:00
-- url     : https://prove2.me/theorems/eb36bd30-8eb6-4a8f-9a2f-3f6b95e78222
-- title:
--   Graph Conjecture84: exists cut vertex of min Degree eq one
-- statement:
--   In order at least three, the neighbor of a leaf is a vertex cut.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L93-L123
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L93-L123

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

theorem WrittenOnTheWallII.GraphConjecture84.exists_cut_vertex_of_minDegree_eq_one {G : SimpleGraph α} [DecidableRel G.Adj]
    [Nonempty α] (hδ : G.minDegree = 1) (hcard : 3 ≤ Fintype.card α) :
    ∃ v, ¬ (G.induce ({v}ᶜ : Set α)).Connected := by sorry
