-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_delete_endPoint_connected
-- name    : WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.delete_endPoint_connected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:31:10.720806+00:00
-- url     : https://prove2.me/theorems/1529a7d5-6f3f-494d-88c6-d7601fcae2cd
-- title:
--   Pendant Geodesics: delete end Point connected
-- statement:
--   Deleting the endpoint of a positive pendant path preserves connectedness.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1646-L1650
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1646-L1650

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

theorem WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.delete_endPoint_connected (hG : G.Connected) (c : ↥(K : Set α))
    (hpos : 0 < (F.path c).length) :
    (G.induce ({F.endPoint c}ᶜ : Set α)).Connected := by sorry
