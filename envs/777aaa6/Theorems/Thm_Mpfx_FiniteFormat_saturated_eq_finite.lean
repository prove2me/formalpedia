-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_saturated_eq_finite
-- name    : Mpfx.FiniteFormat.saturated_eq_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:29:25.176803+00:00
-- url     : https://prove2.me/theorems/506cf180-f7cd-4c1d-a922-ad52c3141076
-- title:
--   Finite Format: saturated eq finite
-- statement:
--   A value of magnitude `maxFinite` with sign `negative` is the saturated value.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Special.lean#L66-L82
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Special.lean#L66-L82

import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Special
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.saturated_eq_finite (F : FiniteFormat) (hb : F.b ≠ ⊤) {negative : Bool} {w : Dyadic}
    (habs : |(w : ℝ)| = (F.maxFinite hb : ℝ))
    (hsign : (w : ℝ) ≠ 0 → decide ((w : ℚ) < 0) = negative) :
    F.saturated hb negative = .finite w := by sorry
