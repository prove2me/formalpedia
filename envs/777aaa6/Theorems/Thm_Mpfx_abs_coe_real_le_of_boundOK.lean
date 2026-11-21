-- Prove2me | Theorems.Thm_Mpfx_abs_coe_real_le_of_boundOK
-- name    : Mpfx.abs_coe_real_le_of_boundOK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:25:41.15661+00:00
-- url     : https://prove2.me/theorems/52452885-751a-431c-b12b-2f3cbc60d803
-- title:
--   Mpfx: abs coe real le of bound OK
-- statement:
--   A bound check against a finite bound, transferred to an absolute-value
--   bound over `ℝ`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L593-L596
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L593-L596

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.abs_coe_real_le_of_boundOK {b₁ : NonNegDyadic} {y : Dyadic}
    (h : Format.boundOK ((b₁ : Bound)) y) :
    |(y : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ) := by sorry
