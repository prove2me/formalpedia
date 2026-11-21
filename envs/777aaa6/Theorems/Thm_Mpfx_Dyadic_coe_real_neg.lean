-- Prove2me | Theorems.Thm_Mpfx_Dyadic_coe_real_neg
-- name    : Mpfx.Dyadic.coe_real_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:19:47.495776+00:00
-- url     : https://prove2.me/theorems/ac5027d9-a50f-41a1-8090-1d5e8059da8e
-- title:
--   Dyadic: coe real neg
-- statement:
--   Coercion of negation, all the way to ℝ.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L111-L113
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L111-L113

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

theorem Mpfx.Dyadic.coe_real_neg (d : Dyadic) :
    ((-d : Dyadic) : ℝ) = -((d : Dyadic) : ℝ) := by sorry
