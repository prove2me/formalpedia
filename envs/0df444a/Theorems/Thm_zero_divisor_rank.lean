-- Prove2me | Theorems.Thm_zero_divisor_rank
-- name    : zero_divisor_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:48:29.083232+00:00
-- url     : https://prove2.me/theorems/c9ace702-63f2-4163-85c4-0d3f0e6bb4e7
-- title:
--   zero divisor rank: zero divisor rank
-- statement:
--   The rank of the zero divisor is zero.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L320-L330
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L320-L330

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem zero_divisor_rank (G : CFGraph) : rank G (0:CFDiv G) = 0 := by sorry
