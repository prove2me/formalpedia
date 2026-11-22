-- Prove2me | Theorems.Thm_P2M_Fpy_DigitBound_forall__one_4f65dee80d02
-- name    : P2M_Fpy_DigitBound_forall__one_4f65dee80d02
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:18:00.518566+00:00
-- url     : https://prove2.me/theorems/19c06fa4-fcd9-406f-a924-543469d345be
-- title:
--   P2 M Fpy Digit Bound forall  one 4f65dee80d02: P2 M Fpy Digit Bound forall  one 4f65dee80d02
-- statement:
--   The P2 M Fpy Digit Bound forall  one 4f65dee80d02 construction uses the P2 M Fpy Digit Bound forall  one 4f65dee80d02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L289-L291
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L289-L291

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem P2M_Fpy_DigitBound_forall__one_4f65dee80d02 {α β : Type} {R : α → β → Prop} {a : α} {l : List β}
    (h : List.Forall₂ R [a] l) : ∃ b, l = [b] ∧ R a b := by sorry

alias «Fpy».«DigitBound».«forall₂_one» := P2M_Fpy_DigitBound_forall__one_4f65dee80d02
