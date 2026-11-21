-- Prove2me | Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg
-- name    : Mpfx.Dyadic.precisionAtMost_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:28:36.901367+00:00
-- url     : https://prove2.me/theorems/d04593a2-fe36-4038-8203-faf60563cc95
-- title:
--   Dyadic: precision At Most neg
-- statement:
--   The Dyadic construction uses the precision At Most neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L289-L297
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L289-L297

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

theorem Mpfx.Dyadic.precisionAtMost_neg {p : Prec} {x : Dyadic} (h : precisionAtMost p x) :
    precisionAtMost p (-x) := by sorry
