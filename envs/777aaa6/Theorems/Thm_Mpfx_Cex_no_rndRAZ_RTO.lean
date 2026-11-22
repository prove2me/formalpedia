-- Prove2me | Theorems.Thm_Mpfx_Cex_no_rndRAZ_RTO
-- name    : Mpfx.Cex.no_rndRAZ_RTO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:03:30.053697+00:00
-- url     : https://prove2.me/theorems/c15f8853-bb0e-4c20-b538-a68ec2ae84d1
-- title:
--   Cex: no rnd RAZ RTO
-- statement:
--   `no_roundsRAZ_RTO` on `rnd`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L501-L509
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L501-L509

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_rndRAZ_RTO (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ .awayZero (.finite x) = .value (.finite z) ∧
      rnd F₁.toFiniteFormat S₁ O₁ .toOdd (.finite (z : ℝ)) ≠
        rnd F₁.toFiniteFormat S₁ O₁ .toOdd (.finite x) := by sorry
