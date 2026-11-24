-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_add_dist_eq_of_mem_geodesic
-- name    : WrittenOnTheWallII.GraphConjecture84.dist_add_dist_eq_of_mem_geodesic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:23:16.975131+00:00
-- url     : https://prove2.me/theorems/e3216b2e-dacd-4de4-b801-1ec67a4533fd
-- title:
--   Graph Conjecture84: dist add dist eq of mem geodesic
-- statement:
--   Distances add at every vertex on a geodesic.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L185-L191
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L185-L191

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

theorem WrittenOnTheWallII.GraphConjecture84.dist_add_dist_eq_of_mem_geodesic {G : SimpleGraph α} {u v z : α}
    (p : G.Walk u v) (hp : p.length = G.dist u v) (hz : z ∈ p.support) :
    G.dist u z + G.dist z v = G.dist u v := by sorry
