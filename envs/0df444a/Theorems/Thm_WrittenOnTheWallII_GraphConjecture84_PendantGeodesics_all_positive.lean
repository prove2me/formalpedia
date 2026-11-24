-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_all_positive
-- name    : WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.all_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:31:36.863078+00:00
-- url     : https://prove2.me/theorems/ca459111-5124-4c05-840a-664a8afb1e49
-- title:
--   Pendant Geodesics: all positive
-- statement:
--   Connectedness propagates positivity from one pendant root to every core vertex.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1767-L1782
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1767-L1782

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

theorem WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.all_positive (hG : G.Connected) (hcard : 3 ≤ K.card)
    (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (hdelete : DeletionCenters G) (hr : 1 ≤ G.radius.toNat)
    (hcut : ∃ x, ¬ (G.induce ({x}ᶜ : Set α)).Connected) :
    ∀ c, 0 < (F.path c).length := by sorry
