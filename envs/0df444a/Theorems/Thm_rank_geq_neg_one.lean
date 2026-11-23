-- Prove2me | Theorems.Thm_rank_geq_neg_one
-- name    : rank_geq_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:46:22.177025+00:00
-- url     : https://prove2.me/theorems/0dae8db3-39f6-4ee4-b02f-a1e63e276a7f
-- title:
--   rank geq neg one: rank geq neg one
-- statement:
--   The rank of a divisor is at least $-1$.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L310-L311
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L310-L311

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem rank_geq_neg_one (G : CFGraph) (D : CFDiv G) : rank G D ≥ -1 := by sorry
