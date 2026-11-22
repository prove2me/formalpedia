-- Prove2me | solution 1 for Mpfx.RoundsFinite.unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:29:11.6659+00:00
-- url     : https://prove2.me/submissions/62802ab3-bd20-4391-a61c-2a651ae10195

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_RoundsFinite_unique_toNegative
import Theorems.Thm_Mpfx_RoundsFinite_unique_toPositive
import Theorems.Thm_Mpfx_RoundsFinite_unique_toZero
import Theorems.Thm_Mpfx_RoundsFinite_unique_awayZero
import Theorems.Thm_Mpfx_RoundsFinite_unique_toOdd
import Theorems.Thm_Mpfx_RoundsFinite_unique_nearest

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    (h : ¬ F.IsUndefined rm) {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F.unbounded rm x y₁)
    (h₂ : RoundsFinite F.unbounded rm x y₂) :
    y₁ = y₂ := by
  cases rm with
  | toNegative => exact RoundsFinite.unique_toNegative h₁ h₂
  | toPositive => exact RoundsFinite.unique_toPositive h₁ h₂
  | toZero => exact RoundsFinite.unique_toZero h₁ h₂
  | awayZero => exact RoundsFinite.unique_awayZero h₁ h₂
  | toOdd => exact RoundsFinite.unique_toOdd h h₁ h₂
  | nearest _ => exact RoundsFinite.unique_nearest h h₁ h₂
end RoundsFinite
end Mpfx
