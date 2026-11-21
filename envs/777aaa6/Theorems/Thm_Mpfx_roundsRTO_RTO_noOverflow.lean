-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RTO_noOverflow
-- name    : Mpfx.roundsRTO_RTO_noOverflow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:58:06.825543+00:00
-- url     : https://prove2.me/theorems/13287311-a6a5-4cca-b119-9d5bc9843d48
-- title:
--   Mpfx: rounds RTO RTO no Overflow
-- statement:
--   **rnd-RTO-RTO**, no overflow: if the double rounding stays in bound, so does the
--   direct rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L548-L554
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L548-L554

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RTO_noOverflow {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) (h₁u : ¬ F₁.IsUndefined .toOdd)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .toOdd x z) (hw : RoundsInBound F₁ .toOdd (z : ℝ) w) :
    ¬ Overflows F₁ .toOdd x := by sorry
