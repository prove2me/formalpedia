-- Prove2me | Theorems.Thm_Mpfx_Cex_roundsUp_of_isolated
-- name    : Mpfx.Cex.roundsUp_of_isolated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:50:28.21545+00:00
-- url     : https://prove2.me/theorems/309ea772-3002-4a11-9ff9-557f88d1d648
-- title:
--   Cex: rounds Up of isolated
-- statement:
--   A point at most `2^K` below an isolated value `h` rounds up onto it.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L148-L154
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L148-L154

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.roundsUp_of_isolated {F : FiniteFormat} {h : Dyadic} {K : ℤ} (hK : Isolated F h K)
    (hh : h ∈ F.unbounded) {x : ℝ} (hx : (h : ℝ) - (2 : ℝ) ^ K < x) (hx' : x ≤ h) :
    RoundsFinite F.unbounded .toPositive x h := by sorry
