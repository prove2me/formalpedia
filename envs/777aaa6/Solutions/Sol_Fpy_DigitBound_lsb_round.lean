-- Prove2me | solution 1 for Fpy.DigitBound.lsb_round
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:30:40.268087+00:00
-- url     : https://prove2.me/submissions/4ae9778e-756a-4fc8-b41f-2d01fa63030b

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
import Theorems.Thm_Fpy_DigitBound_EInt_le_of_forall_coe_le
import Theorems.Thm_Fpy_DigitBound_coe_le_lsbOf
import Theorems.Thm_Mpfx_RoundsFinite_mul_zpow_of_mul_zpow


set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}
namespace Fpy.DigitBound
theorem _root_.solution {F : FiniteFormat} {rm : RoundingMode} {x : ℝ} {y : Mpfx.Dyadic}
    (hy : RoundsFinite F.unbounded rm x y) : lsbOf (.finite x) ≤ lsbOf (.finite (y : ℝ)) :=
  EInt.le_of_forall_coe_le fun _ hk => by
    obtain ⟨_, hz⟩ := coe_le_lsbOf.mp hk
    exact coe_le_lsbOf.mpr (hy.mul_zpow_of_mul_zpow hz)
end Fpy.DigitBound
