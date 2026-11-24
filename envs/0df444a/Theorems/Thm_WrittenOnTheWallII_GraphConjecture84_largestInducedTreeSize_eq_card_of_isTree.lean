-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_largestInducedTreeSize_eq_card_of_isTree
-- name    : WrittenOnTheWallII.GraphConjecture84.largestInducedTreeSize_eq_card_of_isTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:27:54.292005+00:00
-- url     : https://prove2.me/theorems/a6a20326-a15a-465a-a5f4-d70034108e27
-- title:
--   Graph Conjecture84: largest Induced Tree Size eq card of is Tree
-- statement:
--   A tree is itself a largest induced tree.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L242-L248
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L242-L248

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

theorem WrittenOnTheWallII.GraphConjecture84.largestInducedTreeSize_eq_card_of_isTree {G : SimpleGraph α} (hG : G.IsTree) :
    largestInducedTreeSize G = Fintype.card α := by sorry
