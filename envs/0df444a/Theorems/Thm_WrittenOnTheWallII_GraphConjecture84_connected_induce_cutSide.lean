-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_connected_induce_cutSide
-- name    : WrittenOnTheWallII.GraphConjecture84.connected_induce_cutSide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:24:38.88826+00:00
-- url     : https://prove2.me/theorems/35cbfb4f-3111-44a2-ac20-ae9d07e82de6
-- title:
--   Graph Conjecture84: connected induce cut Side
-- statement:
--   A side at a cut vertex is connected.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L731-L737
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L731-L737

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

theorem WrittenOnTheWallII.GraphConjecture84.connected_induce_cutSide {G : SimpleGraph α} (hG : G.Connected)
    (c : α) (a : ↥({c}ᶜ : Set α)) : (G.induce (cutSide G c a)).Connected := by sorry
