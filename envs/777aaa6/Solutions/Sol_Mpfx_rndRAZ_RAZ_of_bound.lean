-- Prove2me | solution 1 for Mpfx.rndRAZ_RAZ_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:50:30.402624+00:00
-- url     : https://prove2.me/submissions/e35d5018-837b-41a8-990f-7280e3e969a3

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
import Theorems.Thm_Mpfx_OverflowAgrees_of_bound
import Theorems.Thm_Mpfx_rndRAZ_RAZ
import Theorems.Thm_Mpfx_not_isUndefined_awayZero
import Theorems.Thm_Mpfx_roundsRAZ_RAZ_inBound
import Theorems.Thm_Mpfx_roundsRAZ_RAZ_noOverflow


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hS : S₂.Composes S₁ O₁ .awayZero) (hO : O₂.Composes S₁ O₁ .awayZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .awayZero v = .value u) :
    rnd F₁ S₁ O₁ .awayZero u.toReal = rnd F₁ S₁ O₁ .awayZero v :=
  rndRAZ_RAZ hsub
    (.of_bound (not_isUndefined_awayZero F₁) (not_isUndefined_awayZero F₂)
      (roundsRAZ_RAZ_inBound hsub) fun _ _ _ hz hw => roundsRAZ_RAZ_noOverflow hz hw)
    hS hO hu
end Mpfx
