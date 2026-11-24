-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_delete_zero_connected
-- name    : WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.delete_zero_connected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:30:51.072985+00:00
-- url     : https://prove2.me/theorems/17b3141a-7379-4eb5-b974-0cf3e77d41c1
-- title:
--   Pendant Geodesics: delete zero connected
-- statement:
--   Deleting an unused core root preserves connectedness.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1654-L1692
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1654-L1692

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
include F

theorem WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.delete_zero_connected (hG : G.Connected) (hcard : 3 ≤ K.card)
    (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (a : ↥(K : Set α)) (ha : (F.path a).length = 0) :
    (G.induce ({(a : α)}ᶜ : Set α)).Connected := by sorry
