-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RTO_agree
-- name    : Mpfx.roundsRTO_RTO_agree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:58:42.653475+00:00
-- url     : https://prove2.me/theorems/67f76b37-9305-4c37-91f5-042957bcf02d
-- title:
--   Mpfx: rounds RTO RTO agree
-- statement:
--   **rnd-RTO-RTO**, in bound: the double rounding agrees with the direct rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L661-L666
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L661-L666

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RTO_agree {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) (h₁u : ¬ F₁.IsUndefined .toOdd)
    {x : ℝ} {z w y : Dyadic} (hz : RoundsInBound F₂ .toOdd x z)
    (hw : RoundsInBound F₁ .toOdd (z : ℝ) w) (hy : RoundsInBound F₁ .toOdd x y) :
    w = y := by sorry
