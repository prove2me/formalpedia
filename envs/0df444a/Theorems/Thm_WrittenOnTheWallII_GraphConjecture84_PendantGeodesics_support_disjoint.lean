-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_support_disjoint
-- name    : WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.support_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:25:19.09781+00:00
-- url     : https://prove2.me/theorems/7189d060-e5c9-4965-be5e-19e375af3298
-- title:
--   Pendant Geodesics: support disjoint
-- statement:
--   Distinct core roots have disjoint full pendant supports.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1566-L1574
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1566-L1574

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

theorem WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.support_disjoint (hG : G.Connected) {c d : ↥(K : Set α)} (hcd : c ≠ d) :
    Disjoint (F.path c).support.toFinset (F.path d).support.toFinset := by sorry
