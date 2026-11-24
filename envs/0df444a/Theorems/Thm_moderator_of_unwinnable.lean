-- Prove2me | Theorems.Thm_moderator_of_unwinnable
-- name    : moderator_of_unwinnable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:52:56.618245+00:00
-- url     : https://prove2.me/theorems/7ba764fc-1bb4-4f74-9cb3-4e9d65f7c787
-- title:
--   moderator of unwinnable: moderator of unwinnable
-- statement:
--   For every unwinnable divisor $D$, there exist a moderator $M$ and an effective divisor
--   $H$ with $M \sim D + H$.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L435-L493
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L435-L493

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem moderator_of_unwinnable {G : CFGraph} (h_conn: graph_connected G) (D : CFDiv G) (unwin : ¬ winnable G D) :
  ∃ (M H : CFDiv G), is_moderator M ∧ effective H ∧ linear_equiv G M (D+H) := by sorry
