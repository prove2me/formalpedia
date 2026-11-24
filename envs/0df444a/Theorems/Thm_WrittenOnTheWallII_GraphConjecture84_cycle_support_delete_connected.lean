-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_cycle_support_delete_connected
-- name    : WrittenOnTheWallII.GraphConjecture84.cycle_support_delete_connected
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:29:41.257494+00:00
-- url     : https://prove2.me/theorems/ba75b74a-aab3-46f7-ab7d-ad58485ebd09
-- title:
--   Graph Conjecture84: cycle support delete connected
-- statement:
--   Deleting any vertex from the graph induced by a cycle's support leaves a connected graph.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L957-L1013
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L957-L1013

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

theorem WrittenOnTheWallII.GraphConjecture84.cycle_support_delete_connected {G : SimpleGraph α} {u : α} (p : G.Walk u u)
    (hp : p.IsCycle) (x : ↥(p.support.toFinset : Set α)) :
    ((G.induce (p.support.toFinset : Set α)).induce ({x}ᶜ : Set ↥(p.support.toFinset : Set α))).Connected := by sorry
