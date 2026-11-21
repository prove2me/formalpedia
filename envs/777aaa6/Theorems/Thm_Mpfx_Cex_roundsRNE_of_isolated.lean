-- Prove2me | Theorems.Thm_Mpfx_Cex_roundsRNE_of_isolated
-- name    : Mpfx.Cex.roundsRNE_of_isolated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:47:01.735176+00:00
-- url     : https://prove2.me/theorems/6d1db19e-5c6c-434d-ade7-5648d3a67c7f
-- title:
--   Cex: rounds RNE of isolated
-- statement:
--   A point within `2^K / 2` of an isolated value `h` rounds nearest onto it,
--   with no tie.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L158-L177
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L158-L177

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.roundsRNE_of_isolated {F : FiniteFormat} {h : Dyadic} {K : ℤ} (hK : Isolated F h K)
    (hh : h ∈ F.unbounded) {x : ℝ} (hx : |x - h| < (2 : ℝ) ^ K / 2) :
    RoundsFinite F.unbounded (.nearest .toEven) x h := by sorry
