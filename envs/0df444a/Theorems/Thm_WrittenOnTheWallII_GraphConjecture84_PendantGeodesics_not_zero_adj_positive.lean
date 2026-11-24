-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_not_zero_adj_positive
-- name    : WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.not_zero_adj_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:31:27.040907+00:00
-- url     : https://prove2.me/theorems/9d87d8c6-7e28-448b-88a4-b8c1af880c74
-- title:
--   Pendant Geodesics: not zero adj positive
-- statement:
--   Adjacent core roots cannot have a zero length next to a positive length.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1743-L1764
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1743-L1764

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

theorem WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.not_zero_adj_positive (hG : G.Connected) (hcard : 3 ≤ K.card)
    (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (hdelete : DeletionCenters G) (hr : 1 ≤ G.radius.toNat)
    (a b : ↥(K : Set α)) (hab : G.Adj a b)
    (ha : (F.path a).length = 0) (hb : 0 < (F.path b).length) : False := by sorry
