-- Prove2me | Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe_real
-- name    : Mpfx.Dyadic.quantumAtLeast_coe_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:25:18.724003+00:00
-- url     : https://prove2.me/theorems/f174aec9-a16f-4b89-a061-31da6fd64ca7
-- title:
--   Dyadic: quantum At Least coe real
-- statement:
--   `ℝ`-stated companion to `quantumAtLeast_coe`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L238-L246
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L238-L246

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

theorem Mpfx.Dyadic.quantumAtLeast_coe_real (e : ℤ) (x : Dyadic) :
    quantumAtLeast (e : QExp) x ↔
      ∃ c : ℤ, (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := by sorry
