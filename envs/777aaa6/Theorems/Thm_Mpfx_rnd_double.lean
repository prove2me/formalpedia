-- Prove2me | Theorems.Thm_Mpfx_rnd_double
-- name    : Mpfx.rnd_double
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:31:08.972185+00:00
-- url     : https://prove2.me/theorems/5028a899-b45b-49e0-936b-f2a15cef2b1a
-- title:
--   Mpfx: rnd double
-- statement:
--   **Double rounding with special and overflow maps.** Agreement in bound (`hA`), overflow
--   agreement where one side overflows (`hov`), and composing maps give
--   `rnd₁ ∘ rnd₂ = rnd₁` on every input.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L88-L138
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L88-L138

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
set_option autoImplicit true
open Mpfx

theorem Mpfx.rnd_double {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat} {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁)
    (hA : ∀ (x : ℝ) (z w y : Dyadic), RoundsInBound F₂ rm₂ x z →
      RoundsInBound F₁ rm₁ (z : ℝ) w → RoundsInBound F₁ rm₁ x y → w = y)
    (hov : OverflowAgrees F₁ S₁ O₁ rm₁ F₂ O₂ rm₂)
    (hS : S₂.Composes S₁ O₁ rm₁) (hO : O₂.Composes S₁ O₁ rm₁)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic} (hu : rnd F₂ S₂ O₂ rm₂ v = .value u) :
    rnd F₁ S₁ O₁ rm₁ u.toReal = rnd F₁ S₁ O₁ rm₁ v := by sorry
