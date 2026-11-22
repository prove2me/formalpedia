-- Prove2me | Theorems.Thm_Fpy_overflows_iff_of_threshold
-- name    : Fpy.overflows_iff_of_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:38:21.551518+00:00
-- url     : https://prove2.me/theorems/65886186-baa5-4f25-875a-98c346ec4018
-- title:
--   Fpy: overflows iff of threshold
-- statement:
--   Overflow's threshold condition, by monotonicity: if `±θ` round in bound and
--   every input beyond them rounds out of bound, `F` overflows exactly beyond `±θ`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L133-L144
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L133-L144

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.overflows_iff_of_threshold {F : FiniteFormat} {rm : RoundingMode}
    (h : ¬ F.IsUndefined rm) {θ : ℝ} (hlo : Format.boundOK F.b (rndUnbounded F rm (-θ) h))
    (hhi : Format.boundOK F.b (rndUnbounded F rm θ h))
    (hout : ∀ y, y < -θ ∨ θ < y → ¬ Format.boundOK F.b (rndUnbounded F rm y h)) (y : ℝ) :
    Overflows F rm y ↔ y < -θ ∨ θ < y := by sorry
