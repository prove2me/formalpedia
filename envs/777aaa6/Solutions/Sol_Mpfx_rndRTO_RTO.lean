-- Prove2me | solution 1 for Mpfx.rndRTO_RTO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:45:02.978363+00:00
-- url     : https://prove2.me/submissions/22b23919-0b58-4a92-9499-08da65b519b4

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
import Theorems.Thm_Mpfx_rnd_double
import Theorems.Thm_Mpfx_roundsRTO_RTO_agree


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) (h₁u : ¬ F₁.IsUndefined .toOdd)
    (hov : OverflowAgrees F₁ S₁ O₁ .toOdd F₂ O₂ .toOdd)
    (hS : S₂.Composes S₁ O₁ .toOdd) (hO : O₂.Composes S₁ O₁ .toOdd)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ .toOdd u.toReal = rnd F₁ S₁ O₁ .toOdd v :=
  rnd_double h₁u (fun _ _ _ _ => roundsRTO_RTO_agree hsub hp_F₂ h₁u) hov hS hO hu
end Mpfx
