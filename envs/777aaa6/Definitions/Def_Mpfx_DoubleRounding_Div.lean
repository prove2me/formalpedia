-- Prove2me | Definitions.Def_Mpfx_DoubleRounding_Div
-- name    : Mpfx_DoubleRounding_Div
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:47:21.224469+00:00
-- url     : https://prove2.me/theorems/df9286d7-e00f-4ef1-9f44-4e1538469043
-- title:
--   Div
-- statement:
--   Definitions and structural lemmas for Div, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Div.lean

import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
import Definitions.Def_Mpfx_DoubleRounding_Basic
set_option autoImplicit true
namespace Mpfx
abbrev DivPosCase (F₁ F₂ : FiniteFormat) (tb₁ tb₂ : TieBreak) : Prop :=
  ∀ (a b : Dyadic), a ∈ F₁ → b ∈ F₁ → 0 < (a : ℝ) → 0 < (b : ℝ) →
    ∀ (z w : Dyadic), RoundsFinite F₂.unbounded (.nearest tb₂) ((a : ℝ) / (b : ℝ)) z →
      RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w →
      RoundsFinite F₁.unbounded (.nearest tb₁) ((a : ℝ) / (b : ℝ)) w
end Mpfx


