-- Prove2me | Theorems.Thm_Mpfx_OverflowAgrees_of_saturate
-- name    : Mpfx.OverflowAgrees.of_saturate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:37:36.562623+00:00
-- url     : https://prove2.me/theorems/9f4fcb08-3278-4e3a-98be-e94a9506f948
-- title:
--   Overflow Agrees: of saturate
-- statement:
--   Saturating maps agree under the plain containment, for any modes.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L417-L442
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L417-L442

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
set_option autoImplicit true
open Mpfx

theorem Mpfx.OverflowAgrees.of_saturate {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {rm₁ rm₂ : RoundingMode} (hsub : F₁.toFormat ⊆ F₂.toFormat) (hb₁ : F₁.b ≠ ⊤)
    (hb₂ : F₂.b ≠ ⊤) (h₁u : ¬ F₁.IsUndefined rm₁) :
    OverflowAgrees F₁ S₁ (OverflowMap.saturate F₁ hb₁) rm₁
      F₂ (OverflowMap.saturate F₂ hb₂) rm₂ := by sorry
