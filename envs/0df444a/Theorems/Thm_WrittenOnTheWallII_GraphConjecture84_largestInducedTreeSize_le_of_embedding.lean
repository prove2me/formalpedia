-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_largestInducedTreeSize_le_of_embedding
-- name    : WrittenOnTheWallII.GraphConjecture84.largestInducedTreeSize_le_of_embedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:27:26.921829+00:00
-- url     : https://prove2.me/theorems/4646a0e3-f14a-4156-b2fe-f137d95f95ff
-- title:
--   Graph Conjecture84: largest Induced Tree Size le of embedding
-- statement:
--   An induced graph embedding transports induced trees without changing their order.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L64-L84
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L64-L84

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

theorem WrittenOnTheWallII.GraphConjecture84.largestInducedTreeSize_le_of_embedding {β : Type*} [Fintype β] [DecidableEq β]
    {H : SimpleGraph β} {G : SimpleGraph α} (e : H ↪g G) :
    largestInducedTreeSize H ≤ largestInducedTreeSize G := by sorry
