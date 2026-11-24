-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_length_induce_walk
-- name    : WrittenOnTheWallII.GraphConjecture84.length_induce_walk
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:29:19.389244+00:00
-- url     : https://prove2.me/theorems/602bef91-6925-407e-9571-a13793e74cb2
-- title:
--   Graph Conjecture84: length induce walk
-- statement:
--   Restricting a walk to a vertex set preserves its length.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L740-L746
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L740-L746

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

theorem WrittenOnTheWallII.GraphConjecture84.length_induce_walk {G : SimpleGraph α} {S : Set α} {u v : α}
    (p : G.Walk u v) (hp : ∀ z ∈ p.support, z ∈ S) :
    (p.induce S hp).length = p.length := by sorry
