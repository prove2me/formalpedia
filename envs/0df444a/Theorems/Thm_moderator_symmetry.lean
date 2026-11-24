-- Prove2me | Theorems.Thm_moderator_symmetry
-- name    : moderator_symmetry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:52:13.326298+00:00
-- url     : https://prove2.me/theorems/69273381-e60c-490b-9aca-81fbd08c30c0
-- title:
--   moderator symmetry: moderator symmetry
-- statement:
--   If $D$ is a moderator, then so is $K_G - D$ (via the reverse orientation). This is the
--   key duality in the proof of Riemann-Roch.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L413-L421
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L413-L421

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem moderator_symmetry {G : CFGraph} (D : CFDiv G) :
  is_moderator D → is_moderator (canonical_divisor G - D) := by sorry
