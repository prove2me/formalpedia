-- Prove2me | solution 1 for Mpfx.rndRTO_RN_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:50:49.599749+00:00
-- url     : https://prove2.me/submissions/bac73595-7f99-4116-a9d1-a6485ac27835

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
import Theorems.Thm_Mpfx_OverflowAgrees_of_bound
import Theorems.Thm_Mpfx_rndRTO_RN
import Theorems.Thm_Mpfx_extend_two_subset_of_withBound_subset
import Theorems.Thm_Mpfx_not_isUndefined_of_two_le_p
import Theorems.Thm_Mpfx_roundsRTO_RN_inBound
import Theorems.Thm_Mpfx_roundsRTO_RN_noOverflow
import Theorems.Thm_Mpfx_two_le_p_of_nontrivial_extend_two


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat} {tb : TieBreak}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) (h₁u : ¬ F₁.IsUndefined (.nearest tb))
    (hS : S₂.Composes S₁ O₁ (.nearest tb)) (hO : O₂.Composes S₁ O₁ (.nearest tb))
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ (.nearest tb) u.toReal = rnd F₁ S₁ O₁ (.nearest tb) v :=
  have hp_F₂ := two_le_p_of_nontrivial_extend_two hsub hnt
  rndRTO_RN (extend_two_subset_of_withBound_subset hsub) hp_F₂ h₁u
    (.of_bound h₁u (not_isUndefined_of_two_le_p hp_F₂) (roundsRTO_RN_inBound hsub hnt h₁u)
      fun _ _ _ hz hw => roundsRTO_RN_noOverflow hsub hnt h₁u hz hw)
    hS hO hu
end Mpfx
