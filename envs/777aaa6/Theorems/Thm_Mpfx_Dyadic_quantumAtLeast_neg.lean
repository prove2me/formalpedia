-- Prove2me | Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg
-- name    : Mpfx.Dyadic.quantumAtLeast_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:27:57.03268+00:00
-- url     : https://prove2.me/theorems/21d8f75b-9aaf-436d-912e-b4a48d7bdff1
-- title:
--   Dyadic: quantum At Least neg
-- statement:
--   The Dyadic construction uses the quantum At Least neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L303-L310
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L303-L310

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

theorem Mpfx.Dyadic.quantumAtLeast_neg {e : QExp} {x : Dyadic} (h : quantumAtLeast e x) :
    quantumAtLeast e (-x) := by sorry
