-- Prove2me | Theorems.Thm_Mpfx_Cex_le_of_roundsUp_of_isolated
-- name    : Mpfx.Cex.le_of_roundsUp_of_isolated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:59:05.464092+00:00
-- url     : https://prove2.me/theorems/736be560-3d45-4f27-988d-c960a700b1d2
-- title:
--   Cex: le of rounds Up of isolated
-- statement:
--   A round-up of a point less than `2^K` below an isolated `m` is at least
--   `m`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L192-L199
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L192-L199

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.le_of_roundsUp_of_isolated {F : FiniteFormat} {m : Dyadic} {K : ℤ}
    (hK : Isolated F m K) {x : ℝ} {z : Dyadic} (hz : RoundsFinite F.unbounded .toPositive x z)
    (hx : (m : ℝ) - (2 : ℝ) ^ K < x) : (m : ℝ) ≤ z := by sorry
