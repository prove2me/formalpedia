-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_isOdd_iff_odd
-- name    : Mpfx.FiniteFormat.isOdd_iff_odd
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:50:47.734494+00:00
-- url     : https://prove2.me/theorems/a401efec-fd98-49ed-ac82-f75b99b9fbb5
-- title:
--   Finite Format: is Odd iff odd
-- statement:
--   For `p ≠ 1`, `y` is odd iff its significand at the canonical exponent is.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L171-L177
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L171-L177

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.isOdd_iff_odd (F : FiniteFormat) (hp : F.p ≠ ((1 : ℕ) : Prec)) (y : Dyadic) :
    F.IsOdd y ↔ ∃ c : ℤ, (y : ℝ) = c * 2 ^ F.canonicalExp y ∧ Odd c := by sorry
