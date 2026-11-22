-- Prove2me | Theorems.Thm_Mpfx_rndRTO_RTO
-- name    : Mpfx.rndRTO_RTO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:32:58.939172+00:00
-- url     : https://prove2.me/theorems/f4196e5b-e296-4bf5-beb2-6edb26624b23
-- title:
--   Mpfx: rnd RTO RTO
-- statement:
--   **rnd-RTO-RTO** with special and overflow maps.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L219-L229
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L219-L229

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndRTO_RTO {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) (h₁u : ¬ F₁.IsUndefined .toOdd)
    (hov : OverflowAgrees F₁ S₁ O₁ .toOdd F₂ O₂ .toOdd)
    (hS : S₂.Composes S₁ O₁ .toOdd) (hO : O₂.Composes S₁ O₁ .toOdd)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ .toOdd u.toReal = rnd F₁ S₁ O₁ .toOdd v := by sorry
