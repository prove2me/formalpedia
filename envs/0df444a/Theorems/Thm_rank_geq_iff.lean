-- Prove2me | Theorems.Thm_rank_geq_iff
-- name    : rank_geq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:46:13.833519+00:00
-- url     : https://prove2.me/theorems/57ecb390-d267-4441-b3bf-f99e30a0f8a1
-- title:
--   rank geq iff: rank geq iff
-- statement:
--   The relation `rank_geq G D k` is equivalent to the inequality `rank G D ≥ k`.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L258-L267
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L258-L267

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem rank_geq_iff (G : CFGraph) (D : CFDiv G) (k : ℤ) :
  rank_geq G D k ↔ rank G D ≥ k := by sorry
