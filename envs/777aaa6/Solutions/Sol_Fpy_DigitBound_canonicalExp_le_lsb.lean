-- Prove2me | solution 1 for Fpy.DigitBound.canonicalExp_le_lsb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:30:40.787294+00:00
-- url     : https://prove2.me/submissions/e4771e8c-13bc-4ea4-9cc6-e7370718dbd4

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
import Theorems.Thm_Fpy_DigitBound_coe_le_lsbOf
import Theorems.Thm_Mpfx_RoundsFinite_exists_mul_zpow


set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}
namespace Fpy.DigitBound
theorem _root_.solution {F : FiniteFormat} {rm : RoundingMode} {x : ℝ} {y : Mpfx.Dyadic}
    (hy : RoundsFinite F.unbounded rm x y) :
    ((F.canonicalExp x : ℤ) : EInt) ≤ lsbOf (.finite (y : ℝ)) :=
  coe_le_lsbOf.mpr hy.exists_mul_zpow
end Fpy.DigitBound
