-- Prove2me | Theorems.Thm_Mpfx_OverflowMap_saturate_composes
-- name    : Mpfx.OverflowMap.saturate_composes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:31:54.89153+00:00
-- url     : https://prove2.me/theorems/ad9ffc04-cc92-4f3b-822c-ec516ec98234
-- title:
--   Overflow Map: saturate composes
-- statement:
--   Saturating maps compose under the plain containment: `F₁` rounds
--   `±maxFinite₂` onto `±maxFinite₁`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L389-L404
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L389-L404

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
set_option autoImplicit true
open Mpfx

theorem Mpfx.OverflowMap.saturate_composes {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) (hb₁ : F₁.b ≠ ⊤) (hb₂ : F₂.b ≠ ⊤)
    {rm₁ : RoundingMode} (h₁u : ¬ F₁.IsUndefined rm₁) {S₁ : SpecialMap F₁.toFormat} :
    (OverflowMap.saturate F₂ hb₂).Composes S₁ (OverflowMap.saturate F₁ hb₁) rm₁ := by sorry
