-- Prove2me | solution 1 for Mpfx.RoundsFinite.unique_awayZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:13:51.978144+00:00
-- url     : https://prove2.me/submissions/2c940892-e270-4b7c-9e8c-7b33c2250690

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_iff_awayZero_of_nonneg
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_iff_awayZero_of_nonpos
import Theorems.Thm_Mpfx_RoundsFinite_unique_toNegative
import Theorems.Thm_Mpfx_RoundsFinite_unique_toPositive

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution {F : FiniteFormat} {x : ℝ} {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F .awayZero x y₁) (h₂ : RoundsFinite F .awayZero x y₂) :
    y₁ = y₂ := by
  rcases le_total 0 x with hx | hx
  · exact unique_toPositive
      ((RoundsFinite.toPositive_iff_awayZero_of_nonneg F hx y₁).mpr h₁)
      ((RoundsFinite.toPositive_iff_awayZero_of_nonneg F hx y₂).mpr h₂)
  · exact unique_toNegative
      ((RoundsFinite.toNegative_iff_awayZero_of_nonpos F hx y₁).mpr h₁)
      ((RoundsFinite.toNegative_iff_awayZero_of_nonpos F hx y₂).mpr h₂)
end RoundsFinite
end Mpfx
