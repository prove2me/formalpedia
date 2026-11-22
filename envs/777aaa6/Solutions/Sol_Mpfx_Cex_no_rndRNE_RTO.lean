-- Prove2me | solution 1 for Mpfx.Cex.no_rndRNE_RTO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:54:18.516775+00:00
-- url     : https://prove2.me/submissions/3ab5c91d-e989-4627-aec8-7e53178406a0

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
import Theorems.Thm_Mpfx_Cex_Disagrees_rnd_ne
import Theorems.Thm_Mpfx_Cex_no_roundsRNE_RTO
import Theorems.Thm_Mpfx_ParityFormat_not_isUndefined


set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
theorem _root_.solution (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (h₂ : ¬ F₂.IsUndefined (.nearest .toEven))
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ (.nearest .toEven) (.finite x) = .value (.finite z) ∧
      rnd F₁.toFiniteFormat S₁ O₁ .toOdd (.finite (z : ℝ)) ≠
        rnd F₁.toFiniteFormat S₁ O₁ .toOdd (.finite x) :=
  (no_roundsRNE_RTO F₁ h₁ F₂ hsub).rnd_ne h₂
    (F₁.not_isUndefined _) S₂ O₂ S₁ O₁
end Mpfx.Cex
