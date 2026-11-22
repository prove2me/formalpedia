-- Prove2me | Theorems.Thm_Mpfx_Cex_no_rndRAZ_RNE
-- name    : Mpfx.Cex.no_rndRAZ_RNE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:03:43.038634+00:00
-- url     : https://prove2.me/theorems/b94e2dfb-4ade-4bda-ab90-17bec5df8070
-- title:
--   Cex: no rnd RAZ RNE
-- statement:
--   `no_roundsRAZ_RNE` on `rnd`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L546-L554
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L546-L554

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_rndRAZ_RNE (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ .awayZero (.finite x) = .value (.finite z) ∧
      rnd F₁.toFiniteFormat S₁ O₁ (.nearest .toEven) (.finite (z : ℝ)) ≠
        rnd F₁.toFiniteFormat S₁ O₁ (.nearest .toEven) (.finite x) := by sorry
