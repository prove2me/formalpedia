-- Prove2me | Theorems.Thm_P2M_Fpy_DigitBound_forall__two_f1f6dda74e3c
-- name    : P2M_Fpy_DigitBound_forall__two_f1f6dda74e3c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:18:05.94618+00:00
-- url     : https://prove2.me/theorems/c2d416fb-fa6a-423c-be7a-c2497bf93627
-- title:
--   P2 M Fpy Digit Bound forall  two f1f6dda74e3c: P2 M Fpy Digit Bound forall  two f1f6dda74e3c
-- statement:
--   The P2 M Fpy Digit Bound forall  two f1f6dda74e3c construction uses the P2 M Fpy Digit Bound forall  two f1f6dda74e3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L293-L295
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L293-L295

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem P2M_Fpy_DigitBound_forall__two_f1f6dda74e3c {α β : Type} {R : α → β → Prop} {a₁ a₂ : α} {l : List β}
    (h : List.Forall₂ R [a₁, a₂] l) : ∃ b₁ b₂, l = [b₁, b₂] ∧ R a₁ b₁ ∧ R a₂ b₂ := by sorry

alias «Fpy».«DigitBound».«forall₂_two» := P2M_Fpy_DigitBound_forall__two_f1f6dda74e3c
