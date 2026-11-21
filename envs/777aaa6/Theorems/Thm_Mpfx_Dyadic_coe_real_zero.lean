-- Prove2me | Theorems.Thm_Mpfx_Dyadic_coe_real_zero
-- name    : Mpfx.Dyadic.coe_real_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:19:43.272512+00:00
-- url     : https://prove2.me/theorems/a675206a-8cf7-49f4-b4e5-068dcf95e668
-- title:
--   Dyadic: coe real zero
-- statement:
--   Coercion of zero, all the way to ℝ.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L116-L117
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L116-L117

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

theorem Mpfx.Dyadic.coe_real_zero :
    ((0 : Dyadic) : ℝ) = 0 := by sorry
