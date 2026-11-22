-- Prove2me | solution 1 for Mpfx.rndRTO_RAZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:45:35.624383+00:00
-- url     : https://prove2.me/submissions/1eab790a-2679-498a-ab13-1280575e8a94

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
import Theorems.Thm_Mpfx_rnd_double
import Theorems.Thm_Mpfx_not_isUndefined_awayZero
import Theorems.Thm_Mpfx_roundsRTO_RAZ_agree


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat) (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    (hov : OverflowAgrees F₁ S₁ O₁ .awayZero F₂ O₂ .toOdd)
    (hS : S₂.Composes S₁ O₁ .awayZero) (hO : O₂.Composes S₁ O₁ .awayZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ .awayZero u.toReal = rnd F₁ S₁ O₁ .awayZero v :=
  rnd_double (not_isUndefined_awayZero F₁) (fun _ _ _ _ => roundsRTO_RAZ_agree hsub hp_F₂) hov
    hS hO hu
end Mpfx
