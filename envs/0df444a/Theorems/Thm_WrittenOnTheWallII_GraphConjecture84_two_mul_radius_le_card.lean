-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_two_mul_radius_le_card
-- name    : WrittenOnTheWallII.GraphConjecture84.two_mul_radius_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:27:48.784802+00:00
-- url     : https://prove2.me/theorems/bfedd375-28c6-492f-a1f6-58b8a09b8492
-- title:
--   Graph Conjecture84: two mul radius le card
-- statement:
--   Two disjoint geodesics from a center and its neighbor bound twice the radius by order.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L194-L239
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L194-L239

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

theorem WrittenOnTheWallII.GraphConjecture84.two_mul_radius_le_card {G : SimpleGraph α} (hG : G.Connected) :
    2 * G.radius.toNat ≤ Fintype.card α := by sorry
