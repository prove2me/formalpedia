-- Prove2me | Theorems.Thm_Mpfx_Dyadic_precisionAtMost_two_three_zpow
-- name    : Mpfx.Dyadic.precisionAtMost_two_three_zpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:29:42.517532+00:00
-- url     : https://prove2.me/theorems/1f0bec68-21fb-4763-9f1a-14be85ca2d82
-- title:
--   Dyadic: precision At Most two three zpow
-- statement:
--   The dyadic value `3 · 2^k` has precision at most 2 (significand `3` fits
--   in `|c| < 2^2 = 4`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L380-L385
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L380-L385

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

theorem Mpfx.Dyadic.precisionAtMost_two_three_zpow (k : ℤ) :
    precisionAtMost ((2 : ℕ) : Prec) (Dyadic.ofIntZpow 3 k) := by sorry
