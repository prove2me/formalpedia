-- Prove2me | Theorems.Thm_Mpfx_Cex_le_of_roundsDown_of_isolated
-- name    : Mpfx.Cex.le_of_roundsDown_of_isolated
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:58:55.147448+00:00
-- url     : https://prove2.me/theorems/95b5746b-6a1c-44d4-949d-c04523408e13
-- title:
--   Cex: le of rounds Down of isolated
-- statement:
--   A round-down of a point less than `2^K` above an isolated `m` is at most
--   `m`, whether or not `m` is a value.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L181-L188
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L181-L188

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.le_of_roundsDown_of_isolated {F : FiniteFormat} {m : Dyadic} {K : ℤ}
    (hK : Isolated F m K) {x : ℝ} {z : Dyadic} (hz : RoundsFinite F.unbounded .toNegative x z)
    (hx : x < m + (2 : ℝ) ^ K) : (z : ℝ) ≤ m := by sorry
