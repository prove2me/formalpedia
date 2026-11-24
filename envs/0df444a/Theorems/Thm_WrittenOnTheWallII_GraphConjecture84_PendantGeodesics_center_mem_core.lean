-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_center_mem_core
-- name    : WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.center_mem_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:25:59.186483+00:00
-- url     : https://prove2.me/theorems/b5d4f053-a5eb-4792-b430-844f10485ab7
-- title:
--   Pendant Geodesics: center mem core
-- statement:
--   Every original-graph center belongs to the core.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1597-L1627
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1597-L1627

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

theorem WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.center_mem_core (hG : G.Connected) {v : α} (hv : G.eccent v = G.radius) : v ∈ K := by sorry
