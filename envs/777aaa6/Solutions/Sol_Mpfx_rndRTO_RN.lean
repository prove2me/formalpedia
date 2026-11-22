-- Prove2me | solution 1 for Mpfx.rndRTO_RN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:45:54.423718+00:00
-- url     : https://prove2.me/submissions/cff44cfc-27b1-4bf9-be9f-33413f56b51a

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
import Theorems.Thm_Mpfx_rnd_double
import Theorems.Thm_Mpfx_roundsRTO_RN_agree


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat} {tb : TieBreak}
    (hsub : (F₁.extend 2).toFormat ⊆ F₂.toFormat) (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    (h₁u : ¬ F₁.IsUndefined (.nearest tb))
    (hov : OverflowAgrees F₁ S₁ O₁ (.nearest tb) F₂ O₂ .toOdd)
    (hS : S₂.Composes S₁ O₁ (.nearest tb)) (hO : O₂.Composes S₁ O₁ (.nearest tb))
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ (.nearest tb) u.toReal = rnd F₁ S₁ O₁ (.nearest tb) v :=
  rnd_double h₁u (fun _ _ _ _ => roundsRTO_RN_agree hsub hp_F₂ h₁u) hov hS hO hu
end Mpfx
