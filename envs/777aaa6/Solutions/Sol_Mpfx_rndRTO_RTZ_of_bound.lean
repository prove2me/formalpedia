-- Prove2me | solution 1 for Mpfx.rndRTO_RTZ_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:50:38.961506+00:00
-- url     : https://prove2.me/submissions/dc37d9d6-08ed-47e6-b8ec-7dbe9ddbdbe8

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
import Theorems.Thm_Mpfx_OverflowAgrees_of_bound
import Theorems.Thm_Mpfx_rndRTO_RTZ
import Theorems.Thm_Mpfx_extend_one_subset_of_withBound_subset
import Theorems.Thm_Mpfx_not_isUndefined_of_two_le_p
import Theorems.Thm_Mpfx_not_isUndefined_toZero
import Theorems.Thm_Mpfx_roundsRTO_RTZ_inBound
import Theorems.Thm_Mpfx_roundsRTO_RTZ_noOverflow
import Theorems.Thm_Mpfx_two_le_p_of_nontrivial


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial)
    (hS : S₂.Composes S₁ O₁ .toZero) (hO : O₂.Composes S₁ O₁ .toZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ .toZero u.toReal = rnd F₁ S₁ O₁ .toZero v :=
  have hp_F₂ := two_le_p_of_nontrivial hsub hnt
  rndRTO_RTZ (extend_one_subset_of_withBound_subset hsub) hp_F₂
    (.of_bound (not_isUndefined_toZero F₁) (not_isUndefined_of_two_le_p hp_F₂)
      (roundsRTO_RTZ_inBound hsub hnt) fun _ _ _ hz hw => roundsRTO_RTZ_noOverflow hsub hnt hz hw)
    hS hO hu
end Mpfx
