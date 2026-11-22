-- Prove2me | Theorems.Thm_Mpfx_isOdd_alternate_of_bracketing
-- name    : Mpfx.isOdd_alternate_of_bracketing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:48:46.296869+00:00
-- url     : https://prove2.me/theorems/f7f76125-f355-4c24-b1e4-94cf98a74fec
-- title:
--   Mpfx: is Odd alternate of bracketing
-- statement:
--   The `IsOdd` half of `alternate_of_bracketing`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L504-L510
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L504-L510

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.isOdd_alternate_of_bracketing {F : FiniteFormat} {x : ℝ}
    (h : ¬ F.IsUndefined .toOdd) {y y' : Dyadic}
    (hy : RoundsFinite F.unbounded .toNegative x y)
    (hy' : RoundsFinite F.unbounded .toPositive x y')
    (hne : x ≠ (y : ℝ)) :
    (F.IsOdd y' ↔ ¬ F.IsOdd y) := by sorry
