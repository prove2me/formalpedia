-- Prove2me | Theorems.Thm_Mpfx_Dyadic_midpoint_comm
-- name    : Mpfx.Dyadic.midpoint_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:29:28.456777+00:00
-- url     : https://prove2.me/theorems/5a03eaf4-a3a9-4f0c-bf7a-be703ea7e038
-- title:
--   Dyadic: midpoint comm
-- statement:
--   The Dyadic construction uses the midpoint comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L196-L199
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L196-L199

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

theorem Mpfx.Dyadic.midpoint_comm (y₁ y₂ : Dyadic) :
    midpoint y₁ y₂ = midpoint y₂ y₁ := by sorry
