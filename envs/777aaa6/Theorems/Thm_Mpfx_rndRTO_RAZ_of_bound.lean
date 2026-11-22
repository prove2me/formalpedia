-- Prove2me | Theorems.Thm_Mpfx_rndRTO_RAZ_of_bound
-- name    : Mpfx.rndRTO_RAZ_of_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:37:19.872631+00:00
-- url     : https://prove2.me/theorems/3d4a03ea-9d09-4269-a238-a7f64b5382c4
-- title:
--   Mpfx: rnd RTO RAZ of bound
-- statement:
--   **rnd-RTO-RAZ** under the relaxed containment, for any maps.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L290-L303
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L290-L303

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndRTO_RAZ_of_bound {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial)
    (hS : S₂.Composes S₁ O₁ .awayZero) (hO : O₂.Composes S₁ O₁ .awayZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ .awayZero u.toReal = rnd F₁ S₁ O₁ .awayZero v := by sorry
