-- Prove2me | Theorems.Thm_Mpfx_Dyadic_precisionAtMost_of_abs_le
-- name    : Mpfx.Dyadic.precisionAtMost_of_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:28:48.808976+00:00
-- url     : https://prove2.me/theorems/d0dd0389-1d6c-416c-bfd2-2a7473da9ff1
-- title:
--   Dyadic: precision At Most of abs le
-- statement:
--   If `y = c · 2^e` with `|c| ≤ 2^p`, then `precisionAtMost p y`. The
--   boundary case `|c| = 2^p` forces `c = ±2^p`; renormalize to
--   `y = ±1 · 2^(e+p)` to recover a strict-inequality witness.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L416-L436
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L416-L436

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

theorem Mpfx.Dyadic.precisionAtMost_of_abs_le {p : ℕ} (hp : 0 < p) {x : Dyadic} (c e : ℤ)
    (hx : (x : ℚ) = (c : ℚ) * (2 : ℚ) ^ e) (hc : |c| ≤ (2 : ℤ) ^ p) :
    precisionAtMost (p : Prec) x := by sorry
