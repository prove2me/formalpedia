-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_radius_le_radius_induce_of_dominated
-- name    : WrittenOnTheWallII.GraphConjecture84.radius_le_radius_induce_of_dominated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:29:15.019004+00:00
-- url     : https://prove2.me/theorems/028ca625-05d6-48e7-82e3-f62658d7ff5a
-- title:
--   Graph Conjecture84: radius le radius induce of dominated
-- statement:
--   If every discarded vertex is no farther than some retained vertex from each retained
--   vertex, passing to the connected induced graph cannot decrease the radius.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L804-L827
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L804-L827

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

theorem WrittenOnTheWallII.GraphConjecture84.radius_le_radius_induce_of_dominated {G : SimpleGraph α} (hG : G.Connected)
    (S : Set α) [DecidablePred (· ∈ S)] (hS : (G.induce S).Connected)
    (hdom : ∀ v ∈ S, ∀ z ∉ S, ∃ w ∈ S, G.dist v z ≤ G.dist v w) :
    G.radius.toNat ≤ (G.induce S).radius.toNat := by sorry
