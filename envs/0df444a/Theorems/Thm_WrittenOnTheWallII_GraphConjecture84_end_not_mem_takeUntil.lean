-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_end_not_mem_takeUntil
-- name    : WrittenOnTheWallII.GraphConjecture84.end_not_mem_takeUntil
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:29:26.716878+00:00
-- url     : https://prove2.me/theorems/490095de-040f-40b5-9e61-0d5ecd70bb9b
-- title:
--   Graph Conjecture84: end not mem take Until
-- statement:
--   A proper prefix of a path does not contain its terminal vertex.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L947-L954
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L947-L954

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

theorem WrittenOnTheWallII.GraphConjecture84.end_not_mem_takeUntil {G : SimpleGraph α} {u v z : α} (p : G.Walk u v)
    (hp : p.IsPath) (hz : z ∈ p.support) (hzv : z ≠ v) :
    v ∉ (p.takeUntil z hz).support := by sorry
