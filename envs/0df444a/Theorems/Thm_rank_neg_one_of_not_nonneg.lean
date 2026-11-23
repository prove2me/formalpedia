-- Prove2me | Theorems.Thm_rank_neg_one_of_not_nonneg
-- name    : rank_neg_one_of_not_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:48:34.031991+00:00
-- url     : https://prove2.me/theorems/57a01760-7ca1-4596-a69a-9ff326890f0d
-- title:
--   rank neg one of not nonneg: rank neg one of not nonneg
-- statement:
--   If the rank is not nonnegative, then it is $-1$.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L314-L317
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L314-L317

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem rank_neg_one_of_not_nonneg (G : CFGraph) (D : CFDiv G)
  (h_not_nonneg : ¬(rank G D ≥ 0)) : rank G D = -1 := by sorry
