-- Prove2me | solution 1 for Mpfx.Cex.no_rndRAZ_RTZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:54:12.642184+00:00
-- url     : https://prove2.me/submissions/3459c8d9-3c37-4a7c-bf12-38157d9199b8

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
import Theorems.Thm_Mpfx_Cex_Disagrees_rnd_ne
import Theorems.Thm_Mpfx_Cex_no_roundsRAZ_RTZ
import Theorems.Thm_Mpfx_not_isUndefined_awayZero
import Theorems.Thm_Mpfx_not_isUndefined_toZero


set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
theorem _root_.solution (F₁ : FiniteFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ .awayZero (.finite x) = .value (.finite z) ∧
      rnd F₁ S₁ O₁ .toZero (.finite (z : ℝ)) ≠
        rnd F₁ S₁ O₁ .toZero (.finite x) :=
  (no_roundsRAZ_RTZ F₁ h₁ F₂ hsub).rnd_ne (not_isUndefined_awayZero F₂)
    (not_isUndefined_toZero F₁) S₂ O₂ S₁ O₁
end Mpfx.Cex
