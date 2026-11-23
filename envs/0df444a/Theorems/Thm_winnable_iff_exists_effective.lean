-- Prove2me | Theorems.Thm_winnable_iff_exists_effective
-- name    : winnable_iff_exists_effective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:49:08.666535+00:00
-- url     : https://prove2.me/theorems/a3a03269-c6de-4a0f-9223-5e9488e297f7
-- title:
--   winnable iff exists effective: winnable iff exists effective
-- statement:
--   A divisor is winnable if and only if it is linearly equivalent to an effective divisor.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L282-L284
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L282-L284

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem winnable_iff_exists_effective (G : CFGraph) (D : CFDiv G) :
  winnable G D ↔ ∃ D' : CFDiv G, effective D' ∧ linear_equiv G D D' := by sorry
