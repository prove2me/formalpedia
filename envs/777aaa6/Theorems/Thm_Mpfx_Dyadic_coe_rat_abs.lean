-- Prove2me | Theorems.Thm_Mpfx_Dyadic_coe_rat_abs
-- name    : Mpfx.Dyadic.coe_rat_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:20:38.330554+00:00
-- url     : https://prove2.me/theorems/80d92790-f724-44fd-abcb-564933b3b337
-- title:
--   Dyadic: coe rat abs
-- statement:
--   The Dyadic construction uses the coe rat abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L154-L158
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L154-L158

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

theorem Mpfx.Dyadic.coe_rat_abs (x : Dyadic) : ((Dyadic.abs x : Dyadic) : ℚ) = |(x : ℚ)| := by sorry
