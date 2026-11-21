-- Prove2me | Theorems.Thm_Mpfx_Cex_roundsDown_of_isolated
-- name    : Mpfx.Cex.roundsDown_of_isolated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:49:27.434852+00:00
-- url     : https://prove2.me/theorems/58fd810a-2a08-47f7-bbf2-a2e7e44f516e
-- title:
--   Cex: rounds Down of isolated
-- statement:
--   A point at most `2^K` above an isolated value `h` rounds down onto it.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L139-L145
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L139-L145

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.roundsDown_of_isolated {F : FiniteFormat} {h : Dyadic} {K : ℤ} (hK : Isolated F h K)
    (hh : h ∈ F.unbounded) {x : ℝ} (hx : (h : ℝ) ≤ x) (hx' : x < h + (2 : ℝ) ^ K) :
    RoundsFinite F.unbounded .toNegative x h := by sorry
