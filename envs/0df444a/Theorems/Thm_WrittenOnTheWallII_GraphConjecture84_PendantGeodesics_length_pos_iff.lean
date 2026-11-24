-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_length_pos_iff
-- name    : WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.length_pos_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:24:16.948816+00:00
-- url     : https://prove2.me/theorems/d0c9e0a3-fd95-4391-b7a8-bb0e46f94e5f
-- title:
--   Pendant Geodesics: length pos iff
-- statement:
--   A pendant path has positive length precisely when its endpoint differs from its root.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1577-L1586
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1577-L1586

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

theorem WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.length_pos_iff (hG : G.Connected) (c : ↥(K : Set α)) :
    0 < (F.path c).length ↔ F.endPoint c ≠ (c : α) := by sorry
