-- Prove2me | Theorems.Thm_Mpfx_eq_zero_of_coe_real_zero
-- name    : Mpfx.eq_zero_of_coe_real_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:25:22.533167+00:00
-- url     : https://prove2.me/theorems/ddbbd8ad-2e25-4c24-875a-210e642aa0b1
-- title:
--   Mpfx: eq zero of coe real zero
-- statement:
--   A dyadic that is zero over `ℝ` is zero.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L563-L564
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L563-L564

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

theorem Mpfx.eq_zero_of_coe_real_zero {z : Dyadic} (h : (z : ℝ) = 0) : z = 0 := by sorry
