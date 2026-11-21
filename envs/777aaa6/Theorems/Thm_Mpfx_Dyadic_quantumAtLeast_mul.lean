-- Prove2me | Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_mul
-- name    : Mpfx.Dyadic.quantumAtLeast_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:28:08.587364+00:00
-- url     : https://prove2.me/theorems/c5c4bfaf-6044-40ea-bb02-ec35e733c652
-- title:
--   Dyadic: quantum At Least mul
-- statement:
--   A product is quantum-aligned at the *sum* of the operands' quanta.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L340-L354
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L340-L354

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

theorem Mpfx.Dyadic.quantumAtLeast_mul {e₁ e₂ : QExp} {x y : Dyadic}
    (hx : Dyadic.quantumAtLeast e₁ x) (hy : Dyadic.quantumAtLeast e₂ y) :
    Dyadic.quantumAtLeast (e₁ + e₂) (x * y) := by sorry
