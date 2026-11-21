-- Prove2me | Theorems.Thm_Mpfx_Dyadic_coe_midpoint
-- name    : Mpfx.Dyadic.coe_midpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:26:51.40518+00:00
-- url     : https://prove2.me/theorems/096810ef-09ae-4902-91be-812dea59150d
-- title:
--   Dyadic: coe midpoint
-- statement:
--   The Dyadic construction uses the coe midpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L186-L189
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L186-L189

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

theorem Mpfx.Dyadic.coe_midpoint (y₁ y₂ : Dyadic) :
    ((midpoint y₁ y₂ : Dyadic) : ℝ) = ((y₁ : ℝ) + (y₂ : ℝ)) / 2 := by sorry
