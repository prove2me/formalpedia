-- Prove2me | Theorems.Thm_Mpfx_rndRAZ_RAZ
-- name    : Mpfx.rndRAZ_RAZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:32:38.028034+00:00
-- url     : https://prove2.me/theorems/1efd6409-d9cd-42c5-98b5-7f8edb24b4b4
-- title:
--   Mpfx: rnd RAZ RAZ
-- statement:
--   **rnd-RAZ-RAZ** with special and overflow maps.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L192-L202
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L192-L202

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndRAZ_RAZ {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hov : OverflowAgrees F₁ S₁ O₁ .awayZero F₂ O₂ .awayZero)
    (hS : S₂.Composes S₁ O₁ .awayZero) (hO : O₂.Composes S₁ O₁ .awayZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .awayZero v = .value u) :
    rnd F₁ S₁ O₁ .awayZero u.toReal = rnd F₁ S₁ O₁ .awayZero v := by sorry
