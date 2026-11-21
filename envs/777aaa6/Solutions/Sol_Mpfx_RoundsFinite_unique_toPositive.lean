-- Prove2me | solution 1 for Mpfx.RoundsFinite.unique_toPositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:44:46.407768+00:00
-- url     : https://prove2.me/submissions/09708e18-6321-4f67-a1e1-6743fb18f087

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
    (h₁ : RoundsFinite F .toPositive x y₁) (h₂ : RoundsFinite F .toPositive x y₂) :
    y₁ = y₂ := by
  obtain ⟨hm₁, hge₁, hmin₁⟩ := h₁
  obtain ⟨hm₂, hge₂, hmin₂⟩ := h₂
  exact Dyadic.ext_real (le_antisymm (hmin₁ y₂ hm₂ hge₂) (hmin₂ y₁ hm₁ hge₁))
end RoundsFinite
end Mpfx
