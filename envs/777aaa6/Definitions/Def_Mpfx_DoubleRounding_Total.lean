-- Prove2me | Definitions.Def_Mpfx_DoubleRounding_Total
-- name    : Mpfx_DoubleRounding_Total
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:46:27.56877+00:00
-- url     : https://prove2.me/theorems/411d0a60-e144-4df3-b830-08f43f569d13
-- title:
--   Total
-- statement:
--   Definitions and structural lemmas for Total, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
set_option autoImplicit true
namespace Mpfx
structure LocalDoubleRounding (F₁ F₂ : FiniteFormat) (rm₁ rm₂ : RoundingMode)
    (L : ℝ → Prop) : Prop where
  /-- An in-bound direct rounding puts its input in `L`. -/
  pin_direct : ∀ {x : ℝ} {y : Dyadic}, RoundsInBound F₁ rm₁ x y → L x
  /-- An in-bound double rounding puts its input in `L`. -/
  pin_double : ∀ {x : ℝ} {z w : Dyadic}, RoundsInBound F₂ rm₂ x z →
    RoundsInBound F₁ rm₁ (z : ℝ) w → L x
  /-- In `L`, the rounding into `F₂` stays in bound. -/
  bound : ∀ {x : ℝ} {z : Dyadic}, L x → RoundsFinite F₂.unbounded rm₂ x z →
    Format.boundOK F₂.b z
  /-- In `L`, the double rounding is the direct rounding. -/
  agree : ∀ {x : ℝ} {z w y : Dyadic}, L x → RoundsFinite F₂.unbounded rm₂ x z →
    RoundsFinite F₁.unbounded rm₁ (z : ℝ) w → RoundsFinite F₁.unbounded rm₁ x y → w = y
abbrev BelowValue (F₁ : FiniteFormat) (B : Bound) (x : ℝ) : Prop :=
  ∃ T : Dyadic, T ∈ F₁.unbounded ∧ Format.boundOK B T ∧ |x| ≤ T
end Mpfx


