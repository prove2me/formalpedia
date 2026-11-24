-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_endPoint_not_core
-- name    : WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.endPoint_not_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:26:04.375149+00:00
-- url     : https://prove2.me/theorems/a7656114-2d61-400d-b698-2eb85511c8ad
-- title:
--   Pendant Geodesics: end Point not core
-- statement:
--   Endpoints of positive pendant paths are outside the core.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1589-L1593
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1589-L1593

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

theorem WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.endPoint_not_core (hG : G.Connected) (c : ↥(K : Set α))
    (hpos : 0 < (F.path c).length) : F.endPoint c ∉ K := by sorry
