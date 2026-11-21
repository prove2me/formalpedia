-- Prove2me | Theorems.Thm_Mpfx_Dyadic_precisionAtMost_mul
-- name    : Mpfx.Dyadic.precisionAtMost_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:27:50.702946+00:00
-- url     : https://prove2.me/theorems/f45666ee-03c0-432b-819b-6eca75270e95
-- title:
--   Dyadic: precision At Most mul
-- statement:
--   A product needs at most the sum of the operands' precisions.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L357-L376
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L357-L376

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

theorem Mpfx.Dyadic.precisionAtMost_mul {p₁ p₂ : Prec} {x y : Dyadic}
    (hx : precisionAtMost p₁ x) (hy : precisionAtMost p₂ y) :
    precisionAtMost (p₁ + p₂) (x * y) := by sorry
