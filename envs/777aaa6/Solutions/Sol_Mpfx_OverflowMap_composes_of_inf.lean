-- Prove2me | solution 1 for Mpfx.OverflowMap.composes_of_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:50:16.727329+00:00
-- url     : https://prove2.me/submissions/9a0a3581-9a40-4d55-8685-347ac9bd908f

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
import Theorems.Thm_Mpfx_rnd_special
attribute [local simp] Mpfx.WithSpecial.toReal_special
attribute [local simp] Mpfx.rnd_special



set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace OverflowMap
theorem _root_.solution {F₂ F₁ : FiniteFormat} {O₂ : OverflowMap F₂.toFormat}
    {S₁ : SpecialMap F₁.toFormat} {O₁ : OverflowMap F₁.toFormat} {rm₁ : RoundingMode}
    (h₂ : ∀ s, O₂.map s = .special (.inf s)) (hS : ∀ s, S₁.map (.inf s) = .special (.inf s))
    (h₁ : ∀ s, O₁.map s = .special (.inf s)) : O₂.Composes S₁ O₁ rm₁ := fun s => by
  rw [h₂, WithSpecial.toReal_special, rnd_special, hS, h₁]
end OverflowMap
end Mpfx
