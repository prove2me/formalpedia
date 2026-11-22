-- Prove2me | solution 1 for Mpfx.Cex.Disagrees.rnd_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:33:51.826912+00:00
-- url     : https://prove2.me/submissions/67337032-0aa1-4ae4-8e10-02f19ffb4730

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
import Theorems.Thm_Mpfx_rnd_finite_of_roundsFinite


set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
namespace Disagrees
theorem _root_.solution {F₂ F₁ : FiniteFormat} {rm₂ rm₁ : RoundingMode}
    (h : Disagrees F₂ rm₂ F₁ rm₁) (h₂ : ¬ F₂.IsUndefined rm₂) (h₁ : ¬ F₁.IsUndefined rm₁)
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ rm₂ (.finite x) = .value (.finite z) ∧
      rnd F₁ S₁ O₁ rm₁ (.finite (z : ℝ)) ≠ rnd F₁ S₁ O₁ rm₁ (.finite x) := by
  obtain ⟨x, z, w, y, hz, hw, hy, hne⟩ := h
  refine ⟨x, z, by rw [rnd_finite_of_roundsFinite h₂ hz.1, if_pos hz.2], ?_⟩
  rw [rnd_finite_of_roundsFinite h₁ hw.1, if_pos hw.2,
    rnd_finite_of_roundsFinite h₁ hy.1, if_pos hy.2]
  exact fun heq => hne (WithSpecial.finite.inj (RoundResult.value.inj heq))
end Disagrees
end Mpfx.Cex
