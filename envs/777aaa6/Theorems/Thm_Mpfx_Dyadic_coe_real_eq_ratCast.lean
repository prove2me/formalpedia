-- Prove2me | Theorems.Thm_Mpfx_Dyadic_coe_real_eq_ratCast
-- name    : Mpfx.Dyadic.coe_real_eq_ratCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:25:41.400816+00:00
-- url     : https://prove2.me/theorems/f72d788f-e56a-4849-ad88-4e4ab5ed22b4
-- title:
--   Dyadic: coe real eq rat Cast
-- statement:
--   The composite coercion `Dyadic → ℚ → ℝ` is just `((d : ℚ) : ℝ)`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L95-L96
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L95-L96

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

theorem Mpfx.Dyadic.coe_real_eq_ratCast (d : Dyadic) :
    ((d : Dyadic) : ℝ) = ((d : ℚ) : ℝ) := by sorry
