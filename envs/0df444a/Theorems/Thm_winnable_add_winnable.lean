-- Prove2me | Theorems.Thm_winnable_add_winnable
-- name    : winnable_add_winnable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:46:05.562928+00:00
-- url     : https://prove2.me/theorems/6537108a-7fd9-43dc-bda9-3f5580535563
-- title:
--   winnable add winnable: winnable add winnable
-- statement:
--   The sum of two winnable divisors is winnable.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L105-L116
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L105-L116

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem winnable_add_winnable (G : CFGraph) (D1 D2 : CFDiv G)
    (h_winnable1 : winnable G D1) (h_winnable2 : winnable G D2) : winnable G (D1 + D2) := by sorry
