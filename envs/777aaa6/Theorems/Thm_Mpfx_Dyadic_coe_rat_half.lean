-- Prove2me | Theorems.Thm_Mpfx_Dyadic_coe_rat_half
-- name    : Mpfx.Dyadic.coe_rat_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:20:21.436992+00:00
-- url     : https://prove2.me/theorems/8cc14258-4e24-4dcd-9d3b-a89251d842d8
-- title:
--   Dyadic: coe rat half
-- statement:
--   The Dyadic construction uses the coe rat half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L179-L181
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L179-L181

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

theorem Mpfx.Dyadic.coe_rat_half : ((half : Dyadic) : ℚ) = 1 / 2 := by sorry
