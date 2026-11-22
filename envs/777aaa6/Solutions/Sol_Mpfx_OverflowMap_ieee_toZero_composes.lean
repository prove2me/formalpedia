-- Prove2me | solution 1 for Mpfx.OverflowMap.ieee_toZero_composes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:50:52.544176+00:00
-- url     : https://prove2.me/submissions/1437d7ef-275e-4fa4-8d36-4fa6b088a6db

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
import Theorems.Thm_Mpfx_OverflowMap_saturate_composes
import Theorems.Thm_Mpfx_OverflowMap_ieee_toZero
import Theorems.Thm_Mpfx_not_isUndefined_toZero


set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace OverflowMap
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) (hb₁ : F₁.b ≠ ⊤) (hb₂ : F₂.b ≠ ⊤)
    (hinf₁ : ∀ s, Special.inf s ∈ F₁.specials) (hinf₂ : ∀ s, Special.inf s ∈ F₂.specials)
    {S₁ : SpecialMap F₁.toFormat} :
    (OverflowMap.ieee F₂ .toZero hb₂ hinf₂).Composes S₁
      (OverflowMap.ieee F₁ .toZero hb₁ hinf₁) .toZero := by
  rw [OverflowMap.ieee_toZero, OverflowMap.ieee_toZero]
  exact OverflowMap.saturate_composes hsub hb₁ hb₂ (not_isUndefined_toZero F₁)
end OverflowMap
end Mpfx
