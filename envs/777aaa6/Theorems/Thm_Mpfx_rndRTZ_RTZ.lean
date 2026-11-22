-- Prove2me | Theorems.Thm_Mpfx_rndRTZ_RTZ
-- name    : Mpfx.rndRTZ_RTZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:32:22.737545+00:00
-- url     : https://prove2.me/theorems/aa2fd565-8b11-4a78-946e-41eb66c76859
-- title:
--   Mpfx: rnd RTZ RTZ
-- statement:
--   **rnd-RTZ-RTZ** with special and overflow maps: double rounding toward zero is
--   direct rounding toward zero on every input, special or real, overflowing or not.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L166-L175
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L166-L175

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndRTZ_RTZ {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hov : OverflowAgrees F₁ S₁ O₁ .toZero F₂ O₂ .toZero)
    (hS : S₂.Composes S₁ O₁ .toZero) (hO : O₂.Composes S₁ O₁ .toZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toZero v = .value u) :
    rnd F₁ S₁ O₁ .toZero u.toReal = rnd F₁ S₁ O₁ .toZero v := by sorry
