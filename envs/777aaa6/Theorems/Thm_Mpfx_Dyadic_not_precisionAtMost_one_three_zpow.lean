-- Prove2me | Theorems.Thm_Mpfx_Dyadic_not_precisionAtMost_one_three_zpow
-- name    : Mpfx.Dyadic.not_precisionAtMost_one_three_zpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:29:53.804584+00:00
-- url     : https://prove2.me/theorems/42165ed7-1797-42a4-bf5a-99b097cde3ed
-- title:
--   Dyadic: not precision At Most one three zpow
-- statement:
--   The dyadic value `3 · 2^k` is *not* representable at precision 1: `3` is odd
--   and two digits wide.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L624-L626
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L624-L626

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

theorem Mpfx.Dyadic.not_precisionAtMost_one_three_zpow (k : ℤ) :
    ¬ precisionAtMost ((1 : ℕ) : Prec) (Dyadic.ofIntZpow 3 k) := by sorry
