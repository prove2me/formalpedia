-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_isRepresentableAtP_numDigits_iff
-- name    : Mpfx.FiniteFormat.isRepresentableAtP_numDigits_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:55:16.36521+00:00
-- url     : https://prove2.me/theorems/fb8e094f-3440-4a1e-9af5-af829dab2179
-- title:
--   Finite Format: is Representable At P num Digits iff
-- statement:
--   A representation at `y`'s digit count is the one at the canonical
--   exponent.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L104-L154
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L104-L154

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.isRepresentableAtP_numDigits_iff (F : FiniteFormat) {y : Dyadic} {c e : ℤ} :
    Dyadic.IsRepresentableAtP (F.numDigits (y : ℝ)).toNat c e y ↔
      (y : ℝ) ≠ 0 ∧ e = F.canonicalExp y ∧ (y : ℝ) = c * 2 ^ e := by sorry
