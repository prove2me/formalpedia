-- Prove2me | Theorems.Thm_Mpfx_Cex_no_rndRAZ_RTZ
-- name    : Mpfx.Cex.no_rndRAZ_RTZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:03:13.030289+00:00
-- url     : https://prove2.me/theorems/42476ee4-1437-4283-b8a5-12903321db59
-- title:
--   Cex: no rnd RAZ RTZ
-- statement:
--   `no_roundsRAZ_RTZ` on `rnd`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L467-L475
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L467-L475

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_rndRAZ_RTZ (F₁ : FiniteFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ .awayZero (.finite x) = .value (.finite z) ∧
      rnd F₁ S₁ O₁ .toZero (.finite (z : ℝ)) ≠
        rnd F₁ S₁ O₁ .toZero (.finite x) := by sorry
