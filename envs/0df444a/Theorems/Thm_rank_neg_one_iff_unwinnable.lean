-- Prove2me | Theorems.Thm_rank_neg_one_iff_unwinnable
-- name    : rank_neg_one_iff_unwinnable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:46:23.068679+00:00
-- url     : https://prove2.me/theorems/9dd75db0-6801-42a5-9dc5-5cda553e774a
-- title:
--   rank neg one iff unwinnable: rank neg one iff unwinnable
-- statement:
--   A divisor has rank $-1$ if and only if it is not winnable.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L297-L300
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L297-L300

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem rank_neg_one_iff_unwinnable (G : CFGraph) (D : CFDiv G) :
  rank G D = -1 ↔ ¬(winnable G D) := by sorry
