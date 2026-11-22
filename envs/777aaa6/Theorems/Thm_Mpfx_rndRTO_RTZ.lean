-- Prove2me | Theorems.Thm_Mpfx_rndRTO_RTZ
-- name    : Mpfx.rndRTO_RTZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:33:08.083126+00:00
-- url     : https://prove2.me/theorems/ecc55271-d765-4ea5-936b-f93aced74403
-- title:
--   Mpfx: rnd RTO RTZ
-- statement:
--   **rnd-RTO-RTZ** with special and overflow maps. The IEEE maps do not compose here:
--   RTO overflows to `±Inf`, which RTZ keeps, while direct RTZ saturates.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L248-L258
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L248-L258

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndRTO_RTZ {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat) (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    (hov : OverflowAgrees F₁ S₁ O₁ .toZero F₂ O₂ .toOdd)
    (hS : S₂.Composes S₁ O₁ .toZero) (hO : O₂.Composes S₁ O₁ .toZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ .toZero u.toReal = rnd F₁ S₁ O₁ .toZero v := by sorry
