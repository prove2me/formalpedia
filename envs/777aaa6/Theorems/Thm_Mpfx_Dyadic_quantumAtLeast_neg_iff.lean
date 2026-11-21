-- Prove2me | Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
-- name    : Mpfx.Dyadic.quantumAtLeast_neg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:20:58.006548+00:00
-- url     : https://prove2.me/theorems/9d6a94bd-98ca-4780-814b-130acd105c56
-- title:
--   Dyadic: quantum At Least neg iff
-- statement:
--   The Dyadic construction uses the quantum At Least neg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L312-L314
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L312-L314

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

theorem Mpfx.Dyadic.quantumAtLeast_neg_iff (e : QExp) (x : Dyadic) :
    quantumAtLeast e (-x) ↔ quantumAtLeast e x := by sorry
