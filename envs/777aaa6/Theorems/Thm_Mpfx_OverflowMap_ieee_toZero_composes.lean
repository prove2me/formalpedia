-- Prove2me | Theorems.Thm_Mpfx_OverflowMap_ieee_toZero_composes
-- name    : Mpfx.OverflowMap.ieee_toZero_composes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:37:07.400685+00:00
-- url     : https://prove2.me/theorems/5cbac296-f636-4f8b-b096-611582d8b8c2
-- title:
--   Overflow Map: ieee to Zero composes
-- statement:
--   The IEEE RTZ maps compose under the plain containment.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L407-L414
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Special.lean#L407-L414

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
set_option autoImplicit true
open Mpfx

theorem Mpfx.OverflowMap.ieee_toZero_composes {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) (hb₁ : F₁.b ≠ ⊤) (hb₂ : F₂.b ≠ ⊤)
    (hinf₁ : ∀ s, Special.inf s ∈ F₁.specials) (hinf₂ : ∀ s, Special.inf s ∈ F₂.specials)
    {S₁ : SpecialMap F₁.toFormat} :
    (OverflowMap.ieee F₂ .toZero hb₂ hinf₂).Composes S₁
      (OverflowMap.ieee F₁ .toZero hb₁ hinf₁) .toZero := by sorry
