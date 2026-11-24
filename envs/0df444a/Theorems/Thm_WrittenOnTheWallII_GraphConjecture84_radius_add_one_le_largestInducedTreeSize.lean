-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_radius_add_one_le_largestInducedTreeSize
-- name    : WrittenOnTheWallII.GraphConjecture84.radius_add_one_le_largestInducedTreeSize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:23:28.386948+00:00
-- url     : https://prove2.me/theorems/dc113147-52a7-4dd6-834d-27f6a42455c2
-- title:
--   Graph Conjecture84: radius add one le largest Induced Tree Size
-- statement:
--   Radius is attained by a distance in a finite connected graph.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L48-L54
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L48-L54

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

theorem WrittenOnTheWallII.GraphConjecture84.radius_add_one_le_largestInducedTreeSize {G : SimpleGraph α}
    [Nonempty α] (h : G.Connected) :
    G.radius.toNat + 1 ≤ largestInducedTreeSize G := by sorry
