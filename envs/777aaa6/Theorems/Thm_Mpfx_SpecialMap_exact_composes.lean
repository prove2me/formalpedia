-- Prove2me | Theorems.Thm_Mpfx_SpecialMap_exact_composes
-- name    : Mpfx.SpecialMap.exact_composes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:36:35.04183+00:00
-- url     : https://prove2.me/theorems/5d9e5dcd-b60a-478c-b128-701e41f67bb4
-- title:
--   Special Map: exact composes
-- statement:
--   Exact specials compose with any `F₁` map: `F₁` rounds a special by its
--   own map.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L45-L48
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L45-L48

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
set_option autoImplicit true
open Mpfx

theorem Mpfx.SpecialMap.exact_composes {F₂ : FiniteFormat} (h₂ : ∀ s, s ∈ F₂.specials)
    {F₁ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat} {O₁ : OverflowMap F₁.toFormat}
    {rm₁ : RoundingMode} : (SpecialMap.exact F₂.toFormat h₂).Composes S₁ O₁ rm₁ := by sorry
