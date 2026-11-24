-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_dist_from_core
-- name    : WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.dist_from_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:23:42.704292+00:00
-- url     : https://prove2.me/theorems/5729483d-7087-4373-ba09-6023c5ff11e7
-- title:
--   Pendant Geodesics: dist from core
-- statement:
--   Every distance from the core to a pendant path passes through its root.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1554-L1563
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1554-L1563

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

theorem WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.dist_from_core (hG : G.Connected) (c v : ↥(K : Set α)) {z : α}
    (hz : z ∈ (F.path c).support) :
    G.dist v z = G.dist v c + G.dist c z := by sorry
