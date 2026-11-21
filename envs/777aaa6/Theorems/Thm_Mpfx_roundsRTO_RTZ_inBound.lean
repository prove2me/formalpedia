-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RTZ_inBound
-- name    : Mpfx.roundsRTO_RTZ_inBound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:58:11.190003+00:00
-- url     : https://prove2.me/theorems/bfd44d7b-c9db-4072-a41d-1ac1770bab43
-- title:
--   Mpfx: rounds RTO RTZ in Bound
-- statement:
--   **rnd-RTO-RTZ**, total form: the direct rounding overflows, or the rounding into
--   `F₂` and the double rounding stay in bound and agree with it. Nontriviality of `F₁`
--   forces `2 ≤ F₂.p` through the containment.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L559-L568
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L559-L568

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RTZ_inBound {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) (x : ℝ) :
    Overflows F₁ .toZero x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .toOdd x z ∧
      RoundsInBound F₁ .toZero (z : ℝ) w ∧
      RoundsInBound F₁ .toZero x w) := by sorry
