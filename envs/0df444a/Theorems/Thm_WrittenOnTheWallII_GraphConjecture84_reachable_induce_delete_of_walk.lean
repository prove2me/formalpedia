-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_reachable_induce_delete_of_walk
-- name    : WrittenOnTheWallII.GraphConjecture84.reachable_induce_delete_of_walk
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:29:35.964892+00:00
-- url     : https://prove2.me/theorems/e1a83a7e-f971-4c10-96f5-2a6f2a0c6b08
-- title:
--   Graph Conjecture84: reachable induce delete of walk
-- statement:
--   A walk supported in an induced graph and avoiding a vertex lifts to its deletion graph.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1051-L1065
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1051-L1065

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

theorem WrittenOnTheWallII.GraphConjecture84.reachable_induce_delete_of_walk {G : SimpleGraph α} {S : Set α} (x : S)
    (u v : ↥({x}ᶜ : Set S)) (p : G.Walk ((u : S) : α) ((v : S) : α))
    (hS : ∀ z ∈ p.support, z ∈ S) (hx : (x : α) ∉ p.support) :
    ((G.induce S).induce ({x}ᶜ : Set S)).Reachable u v := by sorry
