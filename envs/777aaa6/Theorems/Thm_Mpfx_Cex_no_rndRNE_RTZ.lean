-- Prove2me | Theorems.Thm_Mpfx_Cex_no_rndRNE_RTZ
-- name    : Mpfx.Cex.no_rndRNE_RTZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:02:56.745087+00:00
-- url     : https://prove2.me/theorems/27e3ca73-3d8f-4006-b439-e357e5e8255e
-- title:
--   Cex: no rnd RNE RTZ
-- statement:
--   `no_roundsRNE_RTZ` on `rnd`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L455-L464
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L455-L464

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_rndRNE_RTZ (F₁ : FiniteFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (h₂ : ¬ F₂.IsUndefined (.nearest .toEven))
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ (.nearest .toEven) (.finite x) = .value (.finite z) ∧
      rnd F₁ S₁ O₁ .toZero (.finite (z : ℝ)) ≠
        rnd F₁ S₁ O₁ .toZero (.finite x) := by sorry
