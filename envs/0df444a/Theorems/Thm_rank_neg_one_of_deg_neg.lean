-- Prove2me | Theorems.Thm_rank_neg_one_of_deg_neg
-- name    : rank_neg_one_of_deg_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:48:29.691374+00:00
-- url     : https://prove2.me/theorems/c82d296d-c7ee-49ae-bc49-adbc27efb755
-- title:
--   rank neg one of deg neg: rank neg one of deg neg
-- statement:
--   A divisor of negative degree has rank $-1$, i.e. is unwinnable.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L303-L307
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L303-L307

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem rank_neg_one_of_deg_neg (G : CFGraph) (D : CFDiv G) (h_deg : deg D < 0) :
  rank G D = -1 := by sorry
