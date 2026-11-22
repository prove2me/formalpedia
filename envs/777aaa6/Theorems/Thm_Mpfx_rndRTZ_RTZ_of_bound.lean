-- Prove2me | Theorems.Thm_Mpfx_rndRTZ_RTZ_of_bound
-- name    : Mpfx.rndRTZ_RTZ_of_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:37:14.799926+00:00
-- url     : https://prove2.me/theorems/d183214a-70fe-46ad-bc35-114eccbf0d0f
-- title:
--   Mpfx: rnd RTZ RTZ of bound
-- statement:
--   **rnd-RTZ-RTZ** under the relaxed containment, for any maps.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L178-L189
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L178-L189

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndRTZ_RTZ_of_bound {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hS : S₂.Composes S₁ O₁ .toZero) (hO : O₂.Composes S₁ O₁ .toZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toZero v = .value u) :
    rnd F₁ S₁ O₁ .toZero u.toReal = rnd F₁ S₁ O₁ .toZero v := by sorry
