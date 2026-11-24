-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_adjacent_start_eq_snd_of_geodesic
-- name    : WrittenOnTheWallII.GraphConjecture84.adjacent_start_eq_snd_of_geodesic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:25:09.439171+00:00
-- url     : https://prove2.me/theorems/babd2957-412b-4e29-ae7a-b6e374785da6
-- title:
--   Graph Conjecture84: adjacent start eq snd of geodesic
-- statement:
--   A shortest path has just one neighbor of its initial vertex on its support.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1362-L1379
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1362-L1379

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

theorem WrittenOnTheWallII.GraphConjecture84.adjacent_start_eq_snd_of_geodesic {G : SimpleGraph α} (hG : G.Connected)
    {c b z : α} (q : G.Walk c b) (hq : q.length = G.dist c b)
    (hz : z ∈ q.support) (hcz : G.Adj c z) : z = q.snd := by sorry
