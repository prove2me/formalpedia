-- Prove2me | solution 1 for Mpfx.rndRTZ_RTZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:44:54.026726+00:00
-- url     : https://prove2.me/submissions/b963e474-c29d-452a-ba9a-35f294936480

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
import Theorems.Thm_Mpfx_rnd_double
import Theorems.Thm_Mpfx_not_isUndefined_toZero
import Theorems.Thm_Mpfx_roundsRTZ_RTZ_agree


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hov : OverflowAgrees F₁ S₁ O₁ .toZero F₂ O₂ .toZero)
    (hS : S₂.Composes S₁ O₁ .toZero) (hO : O₂.Composes S₁ O₁ .toZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toZero v = .value u) :
    rnd F₁ S₁ O₁ .toZero u.toReal = rnd F₁ S₁ O₁ .toZero v :=
  rnd_double (not_isUndefined_toZero F₁) (fun _ _ _ _ => roundsRTZ_RTZ_agree hsub) hov hS hO hu
end Mpfx
