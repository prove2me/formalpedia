-- Prove2me | Theorems.Thm_Mpfx_Dyadic_coe_real_lt_zero_iff
-- name    : Mpfx.Dyadic.coe_real_lt_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:26:59.283449+00:00
-- url     : https://prove2.me/theorems/211b988d-558b-4f77-ae78-b0f95cb6da3d
-- title:
--   Dyadic: coe real lt zero iff
-- statement:
--   The Dyadic construction uses the coe real lt zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L98-L99
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L98-L99

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

theorem Mpfx.Dyadic.coe_real_lt_zero_iff (d : Dyadic) : (d : ℝ) < 0 ↔ (d : ℚ) < 0 := by sorry
