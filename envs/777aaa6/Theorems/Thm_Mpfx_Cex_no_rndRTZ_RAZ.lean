-- Prove2me | Theorems.Thm_Mpfx_Cex_no_rndRTZ_RAZ
-- name    : Mpfx.Cex.no_rndRTZ_RAZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:03:07.082644+00:00
-- url     : https://prove2.me/theorems/79277d4c-7e0b-460f-abb8-9ea5d46b2f08
-- title:
--   Cex: no rnd RTZ RAZ
-- statement:
--   `no_roundsRTZ_RAZ` on `rnd`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L478-L486
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L478-L486

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_rndRTZ_RAZ (F₁ : FiniteFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ .toZero (.finite x) = .value (.finite z) ∧
      rnd F₁ S₁ O₁ .awayZero (.finite (z : ℝ)) ≠
        rnd F₁ S₁ O₁ .awayZero (.finite x) := by sorry
