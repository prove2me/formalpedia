-- Prove2me | Theorems.Thm_Mpfx_nonneg_coe_real
-- name    : Mpfx.nonneg_coe_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:27:25.654792+00:00
-- url     : https://prove2.me/theorems/8fa2ceb6-79b9-4e5e-90b5-2dd1a8bbc50c
-- title:
--   Mpfx: nonneg coe real
-- statement:
--   A `NonNegDyadic` is non-negative over `ℝ`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L637-L638
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L637-L638

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

theorem Mpfx.nonneg_coe_real (b : NonNegDyadic) : 0 ≤ ((b.val : Dyadic) : ℝ) := by sorry
