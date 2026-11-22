-- Prove2me | Theorems.Thm_Mpfx_OverflowAgrees_of_bound
-- name    : Mpfx.OverflowAgrees.of_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:30:50.069825+00:00
-- url     : https://prove2.me/theorems/bf8ec28b-8234-4f2f-8983-06a56e78cf7c
-- title:
--   Overflow Agrees: of bound
-- statement:
--   A rule's total form (`hP`) and no-overflow form (`hC`) make every field of
--   `OverflowAgrees` vacuous, for any maps.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L142-L160
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L142-L160

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
set_option autoImplicit true
open Mpfx

theorem Mpfx.OverflowAgrees.of_bound {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {O₂ : OverflowMap F₂.toFormat} {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁) (h₂u : ¬ F₂.IsUndefined rm₂)
    (hP : ∀ x : ℝ, Overflows F₁ rm₁ x ∨
      ∃ z w : Dyadic, RoundsInBound F₂ rm₂ x z ∧ RoundsInBound F₁ rm₁ (z : ℝ) w ∧
        RoundsInBound F₁ rm₁ x w)
    (hC : ∀ (x : ℝ) (z w : Dyadic), RoundsInBound F₂ rm₂ x z →
      RoundsInBound F₁ rm₁ (z : ℝ) w → ¬ Overflows F₁ rm₁ x) :
    OverflowAgrees F₁ S₁ O₁ rm₁ F₂ O₂ rm₂ := by sorry
