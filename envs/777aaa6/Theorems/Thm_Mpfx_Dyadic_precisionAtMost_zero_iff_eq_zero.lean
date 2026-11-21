-- Prove2me | Theorems.Thm_Mpfx_Dyadic_precisionAtMost_zero_iff_eq_zero
-- name    : Mpfx.Dyadic.precisionAtMost_zero_iff_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:28:32.56118+00:00
-- url     : https://prove2.me/theorems/49d9f8b2-b240-4306-935b-8a18ecd52e8c
-- title:
--   Dyadic: precision At Most zero iff eq zero
-- statement:
--   Precision `0` is the trivial format: `|c| < 2^0 = 1` forces `c = 0`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L249-L254
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L249-L254

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

theorem Mpfx.Dyadic.precisionAtMost_zero_iff_eq_zero {x : Dyadic} :
    precisionAtMost (0 : Prec) x ↔ x = 0 := by sorry
