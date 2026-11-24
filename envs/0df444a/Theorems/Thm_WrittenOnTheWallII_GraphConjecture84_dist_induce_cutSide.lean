-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_induce_cutSide
-- name    : WrittenOnTheWallII.GraphConjecture84.dist_induce_cutSide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:33:38.672296+00:00
-- url     : https://prove2.me/theorems/5e2bd940-28ee-4cb1-a51c-03e1c6c94e88
-- title:
--   Graph Conjecture84: dist induce cut Side
-- statement:
--   Distances inside one side of a cut vertex equal their ambient distances.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L749-L800
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L749-L800

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

theorem WrittenOnTheWallII.GraphConjecture84.dist_induce_cutSide {G : SimpleGraph α} (hG : G.Connected)
    (c : α) (a : ↥({c}ᶜ : Set α)) (u v : cutSide G c a) :
    (G.induce (cutSide G c a)).dist u v = G.dist u v := by sorry
