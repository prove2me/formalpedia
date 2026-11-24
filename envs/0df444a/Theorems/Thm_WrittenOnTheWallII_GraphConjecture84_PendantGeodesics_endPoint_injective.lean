-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_endPoint_injective
-- name    : WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.endPoint_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:31:53.986667+00:00
-- url     : https://prove2.me/theorems/a3412f2d-aac0-4a22-b5b5-e46b141a6764
-- title:
--   Pendant Geodesics: end Point injective
-- statement:
--   Distinct pendant roots have distinct endpoints.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1785-L1790
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1785-L1790

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

theorem WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.endPoint_injective (hG : G.Connected) : Function.Injective F.endPoint := by sorry
