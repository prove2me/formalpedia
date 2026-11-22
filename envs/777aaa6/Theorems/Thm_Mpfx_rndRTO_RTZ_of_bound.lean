-- Prove2me | Theorems.Thm_Mpfx_rndRTO_RTZ_of_bound
-- name    : Mpfx.rndRTO_RTZ_of_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:37:10.500555+00:00
-- url     : https://prove2.me/theorems/daa72644-413e-4ba0-962a-51683ca3edc1
-- title:
--   Mpfx: rnd RTO RTZ of bound
-- statement:
--   **rnd-RTO-RTZ** under the relaxed containment, for any maps.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L261-L274
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L261-L274

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndRTO_RTZ_of_bound {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial)
    (hS : S₂.Composes S₁ O₁ .toZero) (hO : O₂.Composes S₁ O₁ .toZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ .toZero u.toReal = rnd F₁ S₁ O₁ .toZero v := by sorry
