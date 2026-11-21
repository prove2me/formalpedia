-- Prove2me | Theorems.Thm_Mpfx_Dyadic_coe_real_sub
-- name    : Mpfx.Dyadic.coe_real_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:20:32.868302+00:00
-- url     : https://prove2.me/theorems/8bb40b72-1ddf-4cc4-8008-f37bbb680943
-- title:
--   Dyadic: coe real sub
-- statement:
--   Coercion of subtraction, all the way to ℝ.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L125-L127
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L125-L127

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

theorem Mpfx.Dyadic.coe_real_sub (d₁ d₂ : Dyadic) :
    ((d₁ - d₂ : Dyadic) : ℝ) = ((d₁ : Dyadic) : ℝ) - ((d₂ : Dyadic) : ℝ) := by sorry
