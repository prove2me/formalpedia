-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_chung_induced_tree_bound
-- name    : WrittenOnTheWallII.GraphConjecture84.chung_induced_tree_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:28:35.879237+00:00
-- url     : https://prove2.me/theorems/1151604c-1c8a-44b2-8fae-bde26362c752
-- title:
--   Graph Conjecture84: chung induced tree bound
-- statement:
--   Chung's induction gives an induced tree of order at least twice the radius minus one.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L574-L602
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L574-L602

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

theorem WrittenOnTheWallII.GraphConjecture84.chung_induced_tree_bound {G : SimpleGraph α} (hG : G.Connected) :
    2 * G.radius.toNat ≤ largestInducedTreeSize G + 1 := by sorry
