-- Prove2me | Theorems.Thm_superstable_sub_chip_unwinnable
-- name    : superstable_sub_chip_unwinnable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:46:59.575808+00:00
-- url     : https://prove2.me/theorems/87989a3a-113a-40e9-a7d8-5200d933746d
-- title:
--   superstable sub chip unwinnable: superstable sub chip unwinnable
-- statement:
--   Subtracting a chip at $q$ from a superstable configuration gives an unwinnable
--   divisor.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L383-L403
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L383-L403

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem superstable_sub_chip_unwinnable {G : CFGraph} (q : G.V) (c : Config G q) :
  superstable G q c →
  ¬winnable G (c.chips - one_chip q) := by sorry
