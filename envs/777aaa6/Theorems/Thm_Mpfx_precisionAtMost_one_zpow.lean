-- Prove2me | Theorems.Thm_Mpfx_precisionAtMost_one_zpow
-- name    : Mpfx.precisionAtMost_one_zpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:26:29.509242+00:00
-- url     : https://prove2.me/theorems/fde033c2-f0af-4be9-bf03-f61545df16db
-- title:
--   Mpfx: precision At Most one zpow
-- statement:
--   `2^k` (any `k`) has precision 1, hence fits any precision bound.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L567-L574
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L567-L574

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

theorem Mpfx.precisionAtMost_one_zpow {p : Prec} (hp : p ≠ 0) (k : ℤ) :
    Dyadic.precisionAtMost p (Dyadic.ofIntZpow 1 k) := by sorry
