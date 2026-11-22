-- Prove2me | solution 1 for Mpfx.Cex.no_rndRTZ_RAZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:54:15.542996+00:00
-- url     : https://prove2.me/submissions/1b27e06d-4770-4723-b3c7-6e036a7d1e77

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
import Theorems.Thm_Mpfx_Cex_Disagrees_rnd_ne
import Theorems.Thm_Mpfx_Cex_no_roundsRTZ_RAZ
import Theorems.Thm_Mpfx_not_isUndefined_awayZero
import Theorems.Thm_Mpfx_not_isUndefined_toZero


set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
theorem _root_.solution (F₁ : FiniteFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ .toZero (.finite x) = .value (.finite z) ∧
      rnd F₁ S₁ O₁ .awayZero (.finite (z : ℝ)) ≠
        rnd F₁ S₁ O₁ .awayZero (.finite x) :=
  (no_roundsRTZ_RAZ F₁ h₁ F₂ hsub).rnd_ne (not_isUndefined_toZero F₂)
    (not_isUndefined_awayZero F₁) S₂ O₂ S₁ O₁
end Mpfx.Cex
