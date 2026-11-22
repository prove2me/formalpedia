-- Prove2me | Theorems.Thm_Fpy_DigitBound_Fresh_mono_right
-- name    : Fpy.DigitBound.Fresh.mono_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:19:38.94706+00:00
-- url     : https://prove2.me/theorems/4d9a196c-d7f4-4249-855c-e55be326a222
-- title:
--   Fresh: mono right
-- statement:
--   The Fresh construction uses the mono right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L135-L137
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L135-L137

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx

theorem Fpy.DigitBound.Fresh.mono_right {n₀ n₁ n₂ : ℕ} {Ψ : List Con} (h : Fresh n₀ n₁ Ψ) (h₁₂ : n₁ ≤ n₂) :
    Fresh n₀ n₂ Ψ := by sorry
