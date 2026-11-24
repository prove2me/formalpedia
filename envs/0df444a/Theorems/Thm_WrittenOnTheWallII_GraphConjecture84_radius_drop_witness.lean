-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_radius_drop_witness
-- name    : WrittenOnTheWallII.GraphConjecture84.radius_drop_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:24:35.914918+00:00
-- url     : https://prove2.me/theorems/335f9947-e5c5-4691-9687-6cb7c8ad1f0b
-- title:
--   Graph Conjecture84: radius drop witness
-- statement:
--   A strict radius decrease on deletion produces a center with a unique farthest vertex.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L126-L182
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L126-L182

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

theorem WrittenOnTheWallII.GraphConjecture84.radius_drop_witness {G : SimpleGraph α} (hG : G.Connected) (x : α)
    (hH : (G.induce ({x}ᶜ : Set α)).Connected)
    (hr : 1 ≤ G.radius.toNat)
    (hdrop : (G.induce ({x}ᶜ : Set α)).radius.toNat ≤ G.radius.toNat - 1) :
    ∃ c : α, c ≠ x ∧ G.eccent c = G.radius ∧ G.dist c x = G.radius.toNat ∧
      ∀ z : α, z ≠ x → G.dist c z ≤ G.radius.toNat - 1 := by sorry
