-- Prove2me | Theorems.Thm_Mpfx_Cex_Disagrees_rnd_ne
-- name    : Mpfx.Cex.Disagrees.rnd_ne
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:46:51.699056+00:00
-- url     : https://prove2.me/theorems/c0153124-9bd0-4b0e-80e4-c4aacc57dc11
-- title:
--   Disagrees: rnd ne
-- statement:
--   A `Disagrees` witness refutes `rnd₁ ∘ rnd₂ = rnd₁` (the conclusion of
--   `rnd_double`) at a finite input with a finite intermediate, for every choice of
--   special-value and overflow maps.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L47-L57
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L47-L57

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.Disagrees.rnd_ne {F₂ F₁ : FiniteFormat} {rm₂ rm₁ : RoundingMode}
    (h : Disagrees F₂ rm₂ F₁ rm₁) (h₂ : ¬ F₂.IsUndefined rm₂) (h₁ : ¬ F₁.IsUndefined rm₁)
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ rm₂ (.finite x) = .value (.finite z) ∧
      rnd F₁ S₁ O₁ rm₁ (.finite (z : ℝ)) ≠ rnd F₁ S₁ O₁ rm₁ (.finite x) := by sorry
