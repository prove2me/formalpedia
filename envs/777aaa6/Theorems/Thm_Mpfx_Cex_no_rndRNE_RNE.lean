-- Prove2me | Theorems.Thm_Mpfx_Cex_no_rndRNE_RNE
-- name    : Mpfx.Cex.no_rndRNE_RNE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:03:54.595749+00:00
-- url     : https://prove2.me/theorems/8374c4a2-0543-4c39-9244-ebc37dc01b81
-- title:
--   Cex: no rnd RNE RNE
-- statement:
--   `no_roundsRNE_RNE` on `rnd`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L557-L566
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L557-L566

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_rndRNE_RNE (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : (F₁.toFiniteFormat.extend 1).toFormat ⊆ F₂.toFormat)
    (h₂ : ¬ F₂.IsUndefined (.nearest .toEven))
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ (.nearest .toEven) (.finite x) = .value (.finite z) ∧
      rnd F₁.toFiniteFormat S₁ O₁ (.nearest .toEven) (.finite (z : ℝ)) ≠
        rnd F₁.toFiniteFormat S₁ O₁ (.nearest .toEven) (.finite x) := by sorry
