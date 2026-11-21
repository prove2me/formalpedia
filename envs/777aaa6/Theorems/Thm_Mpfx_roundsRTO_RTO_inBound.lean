-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RTO_inBound
-- name    : Mpfx.roundsRTO_RTO_inBound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:58:09.308558+00:00
-- url     : https://prove2.me/theorems/53cd0fb5-20a9-4d18-811b-489f6d8b0752
-- title:
--   Mpfx: rounds RTO RTO in Bound
-- statement:
--   **rnd-RTO-RTO**, total form: the direct rounding overflows, or the rounding into
--   `F₂` and the double rounding stay in bound and agree with it.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L535-L544
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L535-L544

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RTO_inBound {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    (h₁u : ¬ F₁.IsUndefined .toOdd) (x : ℝ) :
    Overflows F₁ .toOdd x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .toOdd x z ∧
      RoundsInBound F₁ .toOdd (z : ℝ) w ∧
      RoundsInBound F₁ .toOdd x w) := by sorry
