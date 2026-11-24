-- Prove2me | Theorems.Thm_moderator_degree
-- name    : moderator_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:53:02.884813+00:00
-- url     : https://prove2.me/theorems/c8a42658-35c9-4447-bae1-ed8e73dc6105
-- title:
--   moderator degree: moderator degree
-- statement:
--   Moderators have degree $g-1$.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L424-L426
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L424-L426

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem moderator_degree {G : CFGraph} {D : CFDiv G} (h : is_moderator D) : deg D = genus G - 1 := by sorry
