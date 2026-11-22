-- Prove2me | solution 1 for Mpfx.rndRTZ_RTZ_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:50:20.218472+00:00
-- url     : https://prove2.me/submissions/3d7853da-a91b-4bf7-bf69-ff435c7583e4

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
import Theorems.Thm_Mpfx_OverflowAgrees_of_bound
import Theorems.Thm_Mpfx_rndRTZ_RTZ
import Theorems.Thm_Mpfx_FiniteFormat_subset_withBound_boundAfterNext
import Theorems.Thm_Mpfx_not_isUndefined_toZero
import Theorems.Thm_Mpfx_roundsRTZ_RTZ_inBound
import Theorems.Thm_Mpfx_roundsRTZ_RTZ_noOverflow


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hS : S₂.Composes S₁ O₁ .toZero) (hO : O₂.Composes S₁ O₁ .toZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toZero v = .value u) :
    rnd F₁ S₁ O₁ .toZero u.toReal = rnd F₁ S₁ O₁ .toZero v :=
  rndRTZ_RTZ (F₁.subset_withBound_boundAfterNext.trans hsub)
    (.of_bound (not_isUndefined_toZero F₁) (not_isUndefined_toZero F₂)
      (roundsRTZ_RTZ_inBound hsub) fun _ _ _ hz hw => roundsRTZ_RTZ_noOverflow hsub hz hw)
    hS hO hu
end Mpfx
