-- Prove2me | Theorems.Thm_Fpy_DigitBound_AgreeOut_agree
-- name    : Fpy.DigitBound.AgreeOut.agree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:16:21.683514+00:00
-- url     : https://prove2.me/theorems/38fbb7ef-6163-45ff-aa56-4fc2e7c5f13b
-- title:
--   Agree Out: agree
-- statement:
--   The Agree Out construction uses the agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L88-L89
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L88-L89

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx

theorem Fpy.DigitBound.AgreeOut.agree {n₀ n₁ : ℕ} {ι ι' : Asgn} (h : AgreeOut n₀ n₁ ι ι') : Agree n₀ ι ι' := by sorry
