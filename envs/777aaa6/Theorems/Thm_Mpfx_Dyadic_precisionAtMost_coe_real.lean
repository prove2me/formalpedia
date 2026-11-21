-- Prove2me | Theorems.Thm_Mpfx_Dyadic_precisionAtMost_coe_real
-- name    : Mpfx.Dyadic.precisionAtMost_coe_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:25:32.68918+00:00
-- url     : https://prove2.me/theorems/b647c632-8917-4bd3-9a99-34c7b2b38255
-- title:
--   Dyadic: precision At Most coe real
-- statement:
--   `ℝ`-stated companion to `precisionAtMost_coe`. The substrate predicate is
--   `ℚ`-valued; this bridges to `ℝ` for the `Int.log`/`Int.floor` rounding proofs.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L227-L235
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L227-L235

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

theorem Mpfx.Dyadic.precisionAtMost_coe_real (p : ℕ) (x : Dyadic) :
    precisionAtMost (p : Prec) x ↔
      ∃ c e : ℤ, (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ e ∧ |c| < (2 : ℤ) ^ p := by sorry
