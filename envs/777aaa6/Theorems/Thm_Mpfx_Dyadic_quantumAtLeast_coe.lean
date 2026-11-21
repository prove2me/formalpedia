-- Prove2me | Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe
-- name    : Mpfx.Dyadic.quantumAtLeast_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:27:48.095173+00:00
-- url     : https://prove2.me/theorems/f9c003cc-be27-4011-943a-11006be53316
-- title:
--   Dyadic: quantum At Least coe
-- statement:
--   The Dyadic construction uses the quantum At Least coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L221-L223
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L221-L223

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

theorem Mpfx.Dyadic.quantumAtLeast_coe (e : ℤ) (x : Dyadic) :
    quantumAtLeast (e : QExp) x ↔
      ∃ c : ℤ, (x : ℚ) = (c : ℚ) * (2 : ℚ) ^ e := by sorry
