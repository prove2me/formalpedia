-- Prove2me | Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
-- name    : Mpfx.Dyadic.precisionAtMost_neg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:20:41.856745+00:00
-- url     : https://prove2.me/theorems/dc957c96-c557-41b9-a43e-bdb9eba026db
-- title:
--   Dyadic: precision At Most neg iff
-- statement:
--   The Dyadic construction uses the precision At Most neg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L299-L301
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L299-L301

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

theorem Mpfx.Dyadic.precisionAtMost_neg_iff (p : Prec) (x : Dyadic) :
    precisionAtMost p (-x) ↔ precisionAtMost p x := by sorry
