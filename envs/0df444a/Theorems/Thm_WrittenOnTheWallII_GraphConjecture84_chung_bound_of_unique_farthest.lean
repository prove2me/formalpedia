-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_chung_bound_of_unique_farthest
-- name    : WrittenOnTheWallII.GraphConjecture84.chung_bound_of_unique_farthest
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:28:27.870984+00:00
-- url     : https://prove2.me/theorems/7c514c0b-6984-4f5b-80ab-555b8aed3cbf
-- title:
--   Graph Conjecture84: chung bound of unique farthest
-- statement:
--   The two geodesics in Chung's radius-drop argument yield an induced tree on
--   at least twice the radius minus one vertices.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L372-L571
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L372-L571

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
set_option maxHeartbeats 800000

theorem WrittenOnTheWallII.GraphConjecture84.chung_bound_of_unique_farthest {G : SimpleGraph α} (hG : G.Connected)
    {c x : α} (hr : 3 ≤ G.radius.toNat) (hcx : G.dist c x = G.radius.toNat)
    (hother : ∀ z : α, z ≠ x → G.dist c z ≤ G.radius.toNat - 1) :
    2 * G.radius.toNat ≤ largestInducedTreeSize G + 1 := by sorry
