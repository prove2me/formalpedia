-- Prove2me | solution 1 for Mpfx.LocalDoubleRounding.inBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:28:12.006313+00:00
-- url     : https://prove2.me/submissions/ec2a080c-89e9-41bd-b428-8f8b57136061

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
import Theorems.Thm_Mpfx_rndUnbounded_satisfies


set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace LocalDoubleRounding
theorem _root_.solution {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    {L : ℝ → Prop} (h : LocalDoubleRounding F₁ F₂ rm₁ rm₂ L) (h₁u : ¬ F₁.IsUndefined rm₁)
    (h₂u : ¬ F₂.IsUndefined rm₂) (x : ℝ) :
    Overflows F₁ rm₁ x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ rm₂ x z ∧
      RoundsInBound F₁ rm₁ (z : ℝ) w ∧
      RoundsInBound F₁ rm₁ x w) := by
  have hy := rndUnbounded_satisfies F₁ rm₁ x h₁u
  by_cases hb : Format.boundOK F₁.b (rndUnbounded F₁ rm₁ x h₁u)
  · have hL := h.pin_direct ⟨hy, hb⟩
    have hz := rndUnbounded_satisfies F₂ rm₂ x h₂u
    have hw := rndUnbounded_satisfies F₁ rm₁ (rndUnbounded F₂ rm₂ x h₂u : ℝ) h₁u
    have hwy := h.agree hL hz hw hy
    exact Or.inr ⟨_, _, ⟨hz, h.bound hL hz⟩, ⟨hw, hwy ▸ hb⟩, ⟨hwy ▸ hy, hwy ▸ hb⟩⟩
  · exact Or.inl ⟨_, hy, hb⟩
end LocalDoubleRounding
end Mpfx
