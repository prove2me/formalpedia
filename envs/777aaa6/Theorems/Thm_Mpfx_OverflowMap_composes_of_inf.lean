-- Prove2me | Theorems.Thm_Mpfx_OverflowMap_composes_of_inf
-- name    : Mpfx.OverflowMap.composes_of_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:36:38.943032+00:00
-- url     : https://prove2.me/theorems/73fe1a91-6289-4500-9b40-53dbce3baa43
-- title:
--   Overflow Map: composes of inf
-- statement:
--   Overflow maps that both send overflow to `±Inf` compose when `F₁` keeps
--   infinities exact.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L52-L56
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L52-L56

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
set_option autoImplicit true
open Mpfx

theorem Mpfx.OverflowMap.composes_of_inf {F₂ F₁ : FiniteFormat} {O₂ : OverflowMap F₂.toFormat}
    {S₁ : SpecialMap F₁.toFormat} {O₁ : OverflowMap F₁.toFormat} {rm₁ : RoundingMode}
    (h₂ : ∀ s, O₂.map s = .special (.inf s)) (hS : ∀ s, S₁.map (.inf s) = .special (.inf s))
    (h₁ : ∀ s, O₁.map s = .special (.inf s)) : O₂.Composes S₁ O₁ rm₁ := by sorry
