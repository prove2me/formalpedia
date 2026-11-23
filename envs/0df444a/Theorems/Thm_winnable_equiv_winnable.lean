-- Prove2me | Theorems.Thm_winnable_equiv_winnable
-- name    : winnable_equiv_winnable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:46:09.623179+00:00
-- url     : https://prove2.me/theorems/53f995c5-f899-4821-9b6e-5a5bad273f99
-- title:
--   winnable equiv winnable: winnable equiv winnable
-- statement:
--   Winnability is preserved under linear equivalence.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L33-L36
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L33-L36

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem winnable_equiv_winnable (G : CFGraph) (D1 D2 : CFDiv G) :
  winnable G D1 → linear_equiv G D1 D2 → winnable G D2 := by sorry
