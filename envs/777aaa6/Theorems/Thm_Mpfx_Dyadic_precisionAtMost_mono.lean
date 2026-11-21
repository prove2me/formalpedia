-- Prove2me | Theorems.Thm_Mpfx_Dyadic_precisionAtMost_mono
-- name    : Mpfx.Dyadic.precisionAtMost_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:26:57.401338+00:00
-- url     : https://prove2.me/theorems/d63ee034-3ca7-45f8-be42-7cce1012810e
-- title:
--   Dyadic: precision At Most mono
-- statement:
--   `precisionAtMost` is monotone in the precision bound: more precision
--   allowed means the constraint is weaker.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L258-L269
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L258-L269

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic

theorem Mpfx.Dyadic.precisionAtMost_mono {p₁ p₂ : Prec} (h : p₁ ≤ p₂) {x : Dyadic}
    (hx : precisionAtMost p₁ x) : precisionAtMost p₂ x := by sorry
