-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_numDigits_neg
-- name    : Mpfx.FiniteFormat.numDigits_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:30:40.539161+00:00
-- url     : https://prove2.me/theorems/59ebaacf-396e-499c-80b6-9a68cb63aa9a
-- title:
--   Finite Format: num Digits neg
-- statement:
--   The Finite Format construction uses the num Digits neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L570-L572
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L570-L572

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.numDigits_neg (F : FiniteFormat) (x : ℝ) :
    F.numDigits (-x) = F.numDigits x := by sorry
