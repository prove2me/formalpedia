-- Prove2me | solution 1 for Mpfx.RoundsFinite.unique_toNegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:44:28.658362+00:00
-- url     : https://prove2.me/submissions/af752ad2-e868-4614-bfc9-8af92192a10e

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_Dyadic_ext_real


set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution {F : FiniteFormat} {x : ℝ} {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F .toNegative x y₁) (h₂ : RoundsFinite F .toNegative x y₂) :
    y₁ = y₂ := by
  obtain ⟨hm₁, hle₁, hmax₁⟩ := h₁
  obtain ⟨hm₂, hle₂, hmax₂⟩ := h₂
  exact Dyadic.ext_real (le_antisymm (hmax₂ y₁ hm₁ hle₁) (hmax₁ y₂ hm₂ hle₂))
end RoundsFinite
end Mpfx
