-- Prove2me | Theorems.Thm_Mpfx_Cex_no_rndRTZ_RTO
-- name    : Mpfx.Cex.no_rndRTZ_RTO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:03:40.802107+00:00
-- url     : https://prove2.me/theorems/51f75d80-f196-4235-8c3d-92411f362f64
-- title:
--   Cex: no rnd RTZ RTO
-- statement:
--   `no_roundsRTZ_RTO` on `rnd`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L524-L532
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L524-L532

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_rndRTZ_RTO (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 3)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ .toZero (.finite x) = .value (.finite z) ∧
      rnd F₁.toFiniteFormat S₁ O₁ .toOdd (.finite (z : ℝ)) ≠
        rnd F₁.toFiniteFormat S₁ O₁ .toOdd (.finite x) := by sorry
