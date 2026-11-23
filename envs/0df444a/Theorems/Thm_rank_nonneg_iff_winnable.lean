-- Prove2me | Theorems.Thm_rank_nonneg_iff_winnable
-- name    : rank_nonneg_iff_winnable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:46:19.322086+00:00
-- url     : https://prove2.me/theorems/f2193ff0-5c66-46ba-b535-bf69ea685e6d
-- title:
--   rank nonneg iff winnable: rank nonneg iff winnable
-- statement:
--   The inequality $r(D)\ge 0$ holds if and only if $D$ is winnable.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L195-L206
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L195-L206

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem rank_nonneg_iff_winnable (G : CFGraph) (D : CFDiv G) :
  rank_geq G D 0 ↔ winnable G D := by sorry
