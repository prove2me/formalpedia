-- Prove2me | Theorems.Thm_Mpfx_Dyadic_precisionAtMost_coe
-- name    : Mpfx.Dyadic.precisionAtMost_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:25:46.770342+00:00
-- url     : https://prove2.me/theorems/52c4cc7c-89af-4a01-b3ed-7e23bd137a7d
-- title:
--   Dyadic: precision At Most coe
-- statement:
--   The Dyadic construction uses the precision At Most coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L217-L219
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L217-L219

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

theorem Mpfx.Dyadic.precisionAtMost_coe (p : ℕ) (x : Dyadic) :
    precisionAtMost (p : Prec) x ↔
      ∃ c e : ℤ, (x : ℚ) = (c : ℚ) * (2 : ℚ) ^ e ∧ |c| < (2 : ℤ) ^ p := by sorry
