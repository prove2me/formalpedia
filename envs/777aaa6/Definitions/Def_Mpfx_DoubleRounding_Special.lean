-- Prove2me | Definitions.Def_Mpfx_DoubleRounding_Special
-- name    : Mpfx_DoubleRounding_Special
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:29:51.623377+00:00
-- url     : https://prove2.me/theorems/9aa3037b-dc61-4774-93ec-8da665eb812a
-- title:
--   Special
-- statement:
--   Definitions and structural lemmas for Special, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
set_option autoImplicit true
namespace Mpfx
def SpecialMap.Composes {F₂ : FiniteFormat} (S₂ : SpecialMap F₂.toFormat)
    {F₁ : FiniteFormat} (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat)
    (rm₁ : RoundingMode) : Prop :=
  ∀ t, rnd F₁ S₁ O₁ rm₁ (S₂.map t).toReal = .value (S₁.map t)
def OverflowMap.Composes {F₂ : FiniteFormat} (O₂ : OverflowMap F₂.toFormat)
    {F₁ : FiniteFormat} (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat)
    (rm₁ : RoundingMode) : Prop :=
  ∀ negative, rnd F₁ S₁ O₁ rm₁ (O₂.map negative).toReal = .value (O₁.map negative)
structure OverflowAgrees (F₁ : FiniteFormat) (S₁ : SpecialMap F₁.toFormat)
    (O₁ : OverflowMap F₁.toFormat) (rm₁ : RoundingMode)
    (F₂ : FiniteFormat) (O₂ : OverflowMap F₂.toFormat) (rm₂ : RoundingMode) : Prop where
  /-- The double rounding stays in bound and the direct rounding overflows. -/
  direct : ∀ (x : ℝ) (z w : Dyadic), RoundsInBound F₂ rm₂ x z →
    RoundsInBound F₁ rm₁ (z : ℝ) w → Overflows F₁ rm₁ x →
    O₁.map (decide (x < 0)) = .finite w
  /-- `F₂` stays in bound, the double rounding overflows, the direct rounding does not. -/
  double : ∀ (x : ℝ) (z y : Dyadic), RoundsInBound F₂ rm₂ x z → Overflows F₁ rm₁ (z : ℝ) →
    RoundsInBound F₁ rm₁ x y → O₁.map (decide (x < 0)) = .finite y
  /-- `F₂` overflows and the direct rounding does not. -/
  inner : ∀ (x : ℝ) (y : Dyadic), Overflows F₂ rm₂ x → RoundsInBound F₁ rm₁ x y →
    rnd F₁ S₁ O₁ rm₁ (O₂.map (decide (x < 0))).toReal = .value (.finite y)
end Mpfx


