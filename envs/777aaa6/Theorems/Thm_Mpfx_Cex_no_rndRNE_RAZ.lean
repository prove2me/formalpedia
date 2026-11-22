-- Prove2me | Theorems.Thm_Mpfx_Cex_no_rndRNE_RAZ
-- name    : Mpfx.Cex.no_rndRNE_RAZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:03:37.40248+00:00
-- url     : https://prove2.me/theorems/e3356b20-4ebe-4e00-bafc-774979688d9e
-- title:
--   Cex: no rnd RNE RAZ
-- statement:
--   `no_roundsRNE_RAZ` on `rnd`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L489-L498
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L489-L498

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_rndRNE_RAZ (F₁ : FiniteFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (h₂ : ¬ F₂.IsUndefined (.nearest .toEven))
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ (.nearest .toEven) (.finite x) = .value (.finite z) ∧
      rnd F₁ S₁ O₁ .awayZero (.finite (z : ℝ)) ≠
        rnd F₁ S₁ O₁ .awayZero (.finite x) := by sorry
