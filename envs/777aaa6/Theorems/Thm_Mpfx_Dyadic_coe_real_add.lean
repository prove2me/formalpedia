-- Prove2me | Theorems.Thm_Mpfx_Dyadic_coe_real_add
-- name    : Mpfx.Dyadic.coe_real_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:19:46.944065+00:00
-- url     : https://prove2.me/theorems/a04d5a84-6a5c-404c-80b8-acfb4a084563
-- title:
--   Dyadic: coe real add
-- statement:
--   Coercion of addition, all the way to ℝ.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L120-L122
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L120-L122

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

theorem Mpfx.Dyadic.coe_real_add (d₁ d₂ : Dyadic) :
    ((d₁ + d₂ : Dyadic) : ℝ) = ((d₁ : Dyadic) : ℝ) + ((d₂ : Dyadic) : ℝ) := by sorry
