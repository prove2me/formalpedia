-- Prove2me | Theorems.Thm_Mpfx_Dyadic_coe_real_inj
-- name    : Mpfx.Dyadic.coe_real_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:19:44.947178+00:00
-- url     : https://prove2.me/theorems/bdf96df7-8fc9-4376-b1e5-081a96d49788
-- title:
--   Dyadic: coe real inj
-- statement:
--   The Dyadic construction uses the coe real inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L106-L108
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L106-L108

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

theorem Mpfx.Dyadic.coe_real_inj (a b : Dyadic) :
    ((a : Dyadic) : ℝ) = ((b : Dyadic) : ℝ) ↔ a = b := by sorry
