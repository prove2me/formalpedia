-- Prove2me | Theorems.Thm_Mpfx_Dyadic_coe_rat_midpoint
-- name    : Mpfx.Dyadic.coe_rat_midpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:28:33.970781+00:00
-- url     : https://prove2.me/theorems/d3e70896-84c4-4eff-8d9c-1b4817d9a482
-- title:
--   Dyadic: coe rat midpoint
-- statement:
--   The Dyadic construction uses the coe rat midpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L191-L194
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L191-L194

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

theorem Mpfx.Dyadic.coe_rat_midpoint (y₁ y₂ : Dyadic) :
    ((midpoint y₁ y₂ : Dyadic) : ℚ) = (((y₁ : ℚ) + (y₂ : ℚ)) / 2) := by sorry
