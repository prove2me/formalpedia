-- Prove2me | Theorems.Thm_Mpfx_Dyadic_coe_real_mul
-- name    : Mpfx.Dyadic.coe_real_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:19:53.662314+00:00
-- url     : https://prove2.me/theorems/71d5587f-237d-44f0-8f8b-9d512c687402
-- title:
--   Dyadic: coe real mul
-- statement:
--   Coercion of multiplication, all the way to ℝ.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L130-L132
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L130-L132

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

theorem Mpfx.Dyadic.coe_real_mul (d₁ d₂ : Dyadic) :
    ((d₁ * d₂ : Dyadic) : ℝ) = ((d₁ : Dyadic) : ℝ) * ((d₂ : Dyadic) : ℝ) := by sorry
