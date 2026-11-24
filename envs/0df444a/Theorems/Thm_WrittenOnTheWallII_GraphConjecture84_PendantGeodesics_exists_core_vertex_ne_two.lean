-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_exists_core_vertex_ne_two
-- name    : WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.exists_core_vertex_ne_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:24:06.004051+00:00
-- url     : https://prove2.me/theorems/afceca92-d825-4e23-a94a-b167ae1a6be9
-- title:
--   Pendant Geodesics: exists core vertex ne two
-- statement:
--   A core of order at least three has a vertex avoiding two prescribed vertices.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1526-L1537
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1526-L1537

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
open WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
variable {G : SimpleGraph α} {K : Finset α} (F : PendantGeodesics G K)

theorem WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.exists_core_vertex_ne_two (hcard : 3 ≤ K.card) (a b : α) :
    ∃ v : ↥(K : Set α), (v : α) ≠ a ∧ (v : α) ≠ b := by sorry
