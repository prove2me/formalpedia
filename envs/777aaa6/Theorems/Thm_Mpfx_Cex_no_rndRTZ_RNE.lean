-- Prove2me | Theorems.Thm_Mpfx_Cex_no_rndRTZ_RNE
-- name    : Mpfx.Cex.no_rndRTZ_RNE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:03:33.190855+00:00
-- url     : https://prove2.me/theorems/1e8f2f26-db24-4d0b-827f-64b4f9b21e2a
-- title:
--   Cex: no rnd RTZ RNE
-- statement:
--   `no_roundsRTZ_RNE` on `rnd`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L535-L543
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L535-L543

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_rndRTZ_RNE (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ .toZero (.finite x) = .value (.finite z) ∧
      rnd F₁.toFiniteFormat S₁ O₁ (.nearest .toEven) (.finite (z : ℝ)) ≠
        rnd F₁.toFiniteFormat S₁ O₁ (.nearest .toEven) (.finite x) := by sorry
