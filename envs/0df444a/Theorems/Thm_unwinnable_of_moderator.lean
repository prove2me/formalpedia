-- Prove2me | Theorems.Thm_unwinnable_of_moderator
-- name    : unwinnable_of_moderator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:53:14.612236+00:00
-- url     : https://prove2.me/theorems/df972c4b-76b3-45e1-90a7-f06e8883228a
-- title:
--   unwinnable of moderator: unwinnable of moderator
-- statement:
--   Moderators are unwinnable.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L429-L431
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L429-L431

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem unwinnable_of_moderator {G : CFGraph} {D : CFDiv G} (h : is_moderator D) : ¬ winnable G D := by sorry
