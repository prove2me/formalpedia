-- Prove2me | Theorems.Thm_Mpfx_LocalDoubleRounding_inBound
-- name    : Mpfx.LocalDoubleRounding.inBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:47:39.208493+00:00
-- url     : https://prove2.me/theorems/38a6f591-2edb-4547-8b89-20013aa0ae95
-- title:
--   Local Double Rounding: in Bound
-- statement:
--   The total form: the direct rounding overflows, or the rounding into `F₂` and the
--   double rounding stay in bound and agree with it.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L50-L64
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L50-L64

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.LocalDoubleRounding.inBound {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    {L : ℝ → Prop} (h : LocalDoubleRounding F₁ F₂ rm₁ rm₂ L) (h₁u : ¬ F₁.IsUndefined rm₁)
    (h₂u : ¬ F₂.IsUndefined rm₂) (x : ℝ) :
    Overflows F₁ rm₁ x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ rm₂ x z ∧
      RoundsInBound F₁ rm₁ (z : ℝ) w ∧
      RoundsInBound F₁ rm₁ x w) := by sorry
