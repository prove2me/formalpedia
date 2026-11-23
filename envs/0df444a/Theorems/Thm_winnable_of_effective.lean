-- Prove2me | Theorems.Thm_winnable_of_effective
-- name    : winnable_of_effective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:46:10.565728+00:00
-- url     : https://prove2.me/theorems/fef72e5f-dcee-46e0-a9fd-c0cfca786bde
-- title:
--   winnable of effective: winnable of effective
-- statement:
--   Every effective divisor is winnable (take $D' = D$ in the definition).
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L98-L102
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L98-L102

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem winnable_of_effective (G : CFGraph) (D : CFDiv G) (h_eff : effective D) : winnable G D := by sorry
