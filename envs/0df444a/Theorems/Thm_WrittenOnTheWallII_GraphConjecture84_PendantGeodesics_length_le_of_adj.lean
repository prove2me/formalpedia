-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_length_le_of_adj
-- name    : WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.length_le_of_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:31:47.091554+00:00
-- url     : https://prove2.me/theorems/43ec2629-0b28-4be3-97e9-74da276e6212
-- title:
--   Pendant Geodesics: length le of adj
-- statement:
--   Deleting a positive endpoint gives a center witnessing that its length is
--   at least every neighboring pendant length.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1794-L1820
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1794-L1820

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

theorem WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.length_le_of_adj (hG : G.Connected) (hcard : 3 ≤ K.card)
    (hdelete : DeletionCenters G) (hr : 1 ≤ G.radius.toNat)
    (hpos : ∀ c, 0 < (F.path c).length)
    (a b : ↥(K : Set α)) (hab : G.Adj a b) :
    (F.path b).length ≤ (F.path a).length := by sorry
