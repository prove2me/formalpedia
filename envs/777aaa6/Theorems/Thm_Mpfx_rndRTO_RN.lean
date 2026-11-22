-- Prove2me | Theorems.Thm_Mpfx_rndRTO_RN
-- name    : Mpfx.rndRTO_RN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:32:58.230784+00:00
-- url     : https://prove2.me/theorems/15ece1ff-64e1-4556-a4f7-ccfc2b2815d5
-- title:
--   Mpfx: rnd RTO RN
-- statement:
--   **rnd-RTO-RNE** / **rnd-RTO-RNA** with special and overflow maps.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L306-L316
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L306-L316

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndRTO_RN {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat} {tb : TieBreak}
    (hsub : (F₁.extend 2).toFormat ⊆ F₂.toFormat) (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    (h₁u : ¬ F₁.IsUndefined (.nearest tb))
    (hov : OverflowAgrees F₁ S₁ O₁ (.nearest tb) F₂ O₂ .toOdd)
    (hS : S₂.Composes S₁ O₁ (.nearest tb)) (hO : O₂.Composes S₁ O₁ (.nearest tb))
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ (.nearest tb) u.toReal = rnd F₁ S₁ O₁ (.nearest tb) v := by sorry
