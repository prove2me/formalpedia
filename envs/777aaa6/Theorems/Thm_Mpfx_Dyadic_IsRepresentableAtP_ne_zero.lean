-- Prove2me | Theorems.Thm_Mpfx_Dyadic_IsRepresentableAtP_ne_zero
-- name    : Mpfx.Dyadic.IsRepresentableAtP.ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:25:37.536182+00:00
-- url     : https://prove2.me/theorems/f56ec972-c903-4102-b1cd-04bbe27baff6
-- title:
--   Is Representable At P: ne zero
-- statement:
--   `IsRepresentableAtP n c e y` implies `y ≠ 0` (since `|c| ≥ 1`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L439-L451
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L439-L451

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

theorem Mpfx.Dyadic.IsRepresentableAtP.ne_zero {n : ℕ} {c e : ℤ} {y : Dyadic}
    (h : IsRepresentableAtP n c e y) : (y : ℚ) ≠ 0 := by sorry
