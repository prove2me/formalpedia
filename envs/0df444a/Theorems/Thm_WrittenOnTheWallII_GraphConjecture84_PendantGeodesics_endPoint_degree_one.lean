-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_endPoint_degree_one
-- name    : WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.endPoint_degree_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:30:34.14018+00:00
-- url     : https://prove2.me/theorems/c8911c44-2699-45a5-a68d-3bb525b28afc
-- title:
--   Pendant Geodesics: end Point degree one
-- statement:
--   A positive pendant endpoint is a leaf of the whole graph.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1630-L1643
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1630-L1643

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

theorem WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.endPoint_degree_one [DecidableRel G.Adj] (hG : G.Connected) (c : ↥(K : Set α))
    (hpos : 0 < (F.path c).length) : G.degree (F.endPoint c) = 1 := by sorry
