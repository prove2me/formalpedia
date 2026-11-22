-- Prove2me | solution 1 for Mpfx.Cex.no_rndRNE_RAZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:54:15.976672+00:00
-- url     : https://prove2.me/submissions/8d5c0581-f7b3-46ef-b359-1e9959c04437

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
import Theorems.Thm_Mpfx_Cex_Disagrees_rnd_ne
import Theorems.Thm_Mpfx_Cex_no_roundsRNE_RAZ
import Theorems.Thm_Mpfx_not_isUndefined_awayZero


set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
theorem _root_.solution (F₁ : FiniteFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (h₂ : ¬ F₂.IsUndefined (.nearest .toEven))
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ (.nearest .toEven) (.finite x) = .value (.finite z) ∧
      rnd F₁ S₁ O₁ .awayZero (.finite (z : ℝ)) ≠
        rnd F₁ S₁ O₁ .awayZero (.finite x) :=
  (no_roundsRNE_RAZ F₁ h₁ F₂ hsub).rnd_ne h₂
    (not_isUndefined_awayZero F₁) S₂ O₂ S₁ O₁
end Mpfx.Cex
