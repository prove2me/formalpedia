-- Prove2me | Theorems.Thm_Mpfx_rndRTO_RTO_of_bound
-- name    : Mpfx.rndRTO_RTO_of_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:37:19.244788+00:00
-- url     : https://prove2.me/theorems/fcbc9098-1816-4a32-9f8b-44e3ae74283a
-- title:
--   Mpfx: rnd RTO RTO of bound
-- statement:
--   **rnd-RTO-RTO** under the relaxed containment, for any maps.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L232-L244
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L232-L244

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndRTO_RTO_of_bound {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) (h₁u : ¬ F₁.IsUndefined .toOdd)
    (hS : S₂.Composes S₁ O₁ .toOdd) (hO : O₂.Composes S₁ O₁ .toOdd)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ .toOdd u.toReal = rnd F₁ S₁ O₁ .toOdd v := by sorry
