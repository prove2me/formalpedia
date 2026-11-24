-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_reachable_mem_of_adj_closed
-- name    : WrittenOnTheWallII.GraphConjecture84.reachable_mem_of_adj_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:23:32.463798+00:00
-- url     : https://prove2.me/theorems/df9b5db3-3008-4cc8-b303-8dcd8981392d
-- title:
--   Graph Conjecture84: reachable mem of adj closed
-- statement:
--   A set closed under taking neighbors contains every vertex reachable from it.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1272-L1279
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1272-L1279

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

theorem WrittenOnTheWallII.GraphConjecture84.reachable_mem_of_adj_closed {G : SimpleGraph α} {S : Set α}
    (hS : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S) {u v : α}
    (hr : G.Reachable u v) (hu : u ∈ S) : v ∈ S := by sorry
