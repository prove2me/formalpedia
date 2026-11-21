-- Prove2me | Theorems.Thm_Mpfx_Cex_roundsRNE_of_bracket
-- name    : Mpfx.Cex.roundsRNE_of_bracket
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:49:57.630273+00:00
-- url     : https://prove2.me/theorems/a41f5ff3-d2f2-4a90-a22b-6ecd9b199732
-- title:
--   Cex: rounds RNE of bracket
-- statement:
--   Between adjacent values `u < u'`, nearest-even rounding returns the nearer
--   one, and on a tie the even one.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L205-L225
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L205-L225

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.roundsRNE_of_bracket {F : FiniteFormat} {u u' y : Dyadic} {z : ℝ}
    (h : Adjacent F u u') (hzu : (u : ℝ) ≤ z) (hzu' : z ≤ (u' : ℝ)) (hy : y = u ∨ y = u')
    (hclose : |z - y| ≤ |z - u| ∧ |z - y| ≤ |z - u'|)
    (htie : |z - u| = |z - u'| → F.IsEven y) :
    RoundsFinite F.unbounded (.nearest .toEven) z y := by sorry
