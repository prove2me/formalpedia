-- Prove2me | solution 1 for Mpfx.Cex.no_rndRAZ_RTO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:54:17.981022+00:00
-- url     : https://prove2.me/submissions/ed884109-5194-478b-be3e-b15e580692cd

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
import Theorems.Thm_Mpfx_Cex_Disagrees_rnd_ne
import Theorems.Thm_Mpfx_Cex_no_roundsRAZ_RTO
import Theorems.Thm_Mpfx_ParityFormat_not_isUndefined
import Theorems.Thm_Mpfx_not_isUndefined_awayZero


set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
theorem _root_.solution (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ .awayZero (.finite x) = .value (.finite z) ∧
      rnd F₁.toFiniteFormat S₁ O₁ .toOdd (.finite (z : ℝ)) ≠
        rnd F₁.toFiniteFormat S₁ O₁ .toOdd (.finite x) :=
  (no_roundsRAZ_RTO F₁ h₁ F₂ hsub).rnd_ne (not_isUndefined_awayZero F₂)
    (F₁.not_isUndefined _) S₂ O₂ S₁ O₁
end Mpfx.Cex
