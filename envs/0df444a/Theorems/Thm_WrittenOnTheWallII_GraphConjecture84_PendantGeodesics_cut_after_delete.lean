-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_cut_after_delete
-- name    : WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.cut_after_delete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:26:12.100815+00:00
-- url     : https://prove2.me/theorems/577e3770-e00b-4a4c-b141-515f8a954ae9
-- title:
--   Pendant Geodesics: cut after delete
-- statement:
--   A surviving positive tail still certifies a cut after another vertex is deleted.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1695-L1708
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1695-L1708

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

theorem WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.cut_after_delete (hG : G.Connected) (x : α) (c v : ↥(K : Set α))
    (hc : 0 < (F.path c).length) (hcx : (c : α) ≠ x)
    (hex : F.endPoint c ≠ x) (hvc : v ≠ c) (hvx : (v : α) ≠ x) :
    ∃ y, ¬ ((G.induce ({x}ᶜ : Set α)).induce
      ({y}ᶜ : Set ↥({x}ᶜ : Set α))).Connected := by sorry
