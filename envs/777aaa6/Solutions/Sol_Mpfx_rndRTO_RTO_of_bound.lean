-- Prove2me | solution 1 for Mpfx.rndRTO_RTO_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:50:38.446036+00:00
-- url     : https://prove2.me/submissions/28dde47b-23c9-4d01-bc15-d059d0a8f92c

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
import Theorems.Thm_Mpfx_OverflowAgrees_of_bound
import Theorems.Thm_Mpfx_rndRTO_RTO
import Theorems.Thm_Mpfx_FiniteFormat_subset_withBound_boundAfterNext
import Theorems.Thm_Mpfx_not_isUndefined_of_two_le_p
import Theorems.Thm_Mpfx_roundsRTO_RTO_inBound
import Theorems.Thm_Mpfx_roundsRTO_RTO_noOverflow


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) (h₁u : ¬ F₁.IsUndefined .toOdd)
    (hS : S₂.Composes S₁ O₁ .toOdd) (hO : O₂.Composes S₁ O₁ .toOdd)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ .toOdd u.toReal = rnd F₁ S₁ O₁ .toOdd v :=
  rndRTO_RTO (F₁.subset_withBound_boundAfterNext.trans hsub) hp_F₂ h₁u
    (.of_bound h₁u (not_isUndefined_of_two_le_p hp_F₂) (roundsRTO_RTO_inBound hsub hp_F₂ h₁u)
      fun _ _ _ hz hw => roundsRTO_RTO_noOverflow hsub hp_F₂ h₁u hz hw)
    hS hO hu
end Mpfx
