-- Prove2me | Theorems.Thm_Mpfx_NonNegDyadic_le_iff_coe_real
-- name    : Mpfx.NonNegDyadic.le_iff_coe_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:30:00.986098+00:00
-- url     : https://prove2.me/theorems/f91a2525-20f2-4b8d-a890-ed6423f8ae13
-- title:
--   Non Neg Dyadic: le iff coe real
-- statement:
--   The order on `NonNegDyadic`, in terms of the underlying reals.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L631-L634
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L631-L634

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

theorem Mpfx.NonNegDyadic.le_iff_coe_real {a b : NonNegDyadic} :
    a ≤ b ↔ ((a.val : Dyadic) : ℝ) ≤ ((b.val : Dyadic) : ℝ) := by sorry
