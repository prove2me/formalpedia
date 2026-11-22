-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_exists_mul_zpow
-- name    : Mpfx.RoundsFinite.exists_mul_zpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:52:33.314735+00:00
-- url     : https://prove2.me/theorems/6012bd1b-bf82-41fd-9336-8d647a745367
-- title:
--   Rounds Finite: exists mul zpow
-- statement:
--   A rounding of `x` is a multiple of `2^canonicalExp x`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L354-L359
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L354-L359

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.exists_mul_zpow {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F.unbounded rm x y) :
    ∃ c : ℤ, (y : ℝ) = c * (2 : ℝ) ^ F.canonicalExp x := by sorry
