-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_common_length
-- name    : WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.common_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:31:50.075019+00:00
-- url     : https://prove2.me/theorems/bf2a2b02-26d1-4f65-a646-2a1050aa2959
-- title:
--   Pendant Geodesics: common length
-- statement:
--   All positive pendant paths in the minimal counterexample have one common length.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1823-L1840
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1823-L1840

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

theorem WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.common_length (hG : G.Connected) (hcard : 3 ≤ K.card)
    (hK : (G.induce (K : Set α)).Connected)
    (hdelete : DeletionCenters G) (hr : 1 ≤ G.radius.toNat)
    (hpos : ∀ c, 0 < (F.path c).length) :
    ∃ L, 0 < L ∧ ∀ c, (F.path c).length = L := by sorry
