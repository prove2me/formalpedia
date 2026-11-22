-- Prove2me | Theorems.Thm_Mpfx_rndRAZ_RAZ_of_bound
-- name    : Mpfx.rndRAZ_RAZ_of_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:37:17.77605+00:00
-- url     : https://prove2.me/theorems/4a0bbdf1-663a-40f8-81fa-936329f97211
-- title:
--   Mpfx: rnd RAZ RAZ of bound
-- statement:
--   **rnd-RAZ-RAZ** for any maps: `F₂` never overflows where `F₁` does not.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L205-L216
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L205-L216

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndRAZ_RAZ_of_bound {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hS : S₂.Composes S₁ O₁ .awayZero) (hO : O₂.Composes S₁ O₁ .awayZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .awayZero v = .value u) :
    rnd F₁ S₁ O₁ .awayZero u.toReal = rnd F₁ S₁ O₁ .awayZero v := by sorry
