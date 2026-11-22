-- Prove2me | solution 1 for Fpy.DigitBound.msb_add_le_lsb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:34:52.307585+00:00
-- url     : https://prove2.me/submissions/3ececd9c-df28-4768-9d81-1d515fdcee9d

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
import Theorems.Thm_Fpy_DigitBound_coe_add_coe
import Theorems.Thm_Fpy_DigitBound_coe_le_lsbOf
import Theorems.Thm_Fpy_DigitBound_msbOf_le_coe
import Theorems.Thm_Fpy_DigitBound_msbOf_of_ne_zero
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_coe_real
import Theorems.Thm_Mpfx_abs_mul_two_zpow


set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}
namespace Fpy.DigitBound
theorem _root_.solution {F : FiniteFormat} {p : ℕ} (hp : F.p = p) {y : Mpfx.Dyadic}
    (hy : y ∈ F.unbounded) (h0 : (y : ℝ) ≠ 0) :
    msbOf (.finite (y : ℝ)) + ((1 - p : ℤ) : EInt) ≤ lsbOf (.finite (y : ℝ)) := by
  obtain ⟨c, e, hce, hc⟩ := (Dyadic.precisionAtMost_coe_real p y).mp (hp ▸ hy.1)
  refine le_trans ?_ (coe_le_lsbOf.mpr ⟨c, hce⟩)
  have hlt : |(y : ℝ)| < 2 ^ ((e + p - 1 : ℤ) + 1) := by
    rw [hce, abs_mul_two_zpow, show (e + p - 1 : ℤ) + 1 = p + e by ring, zpow_add₀ two_ne_zero,
      zpow_natCast]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hc) (zpow_pos two_pos e)
  have hM := msbOf_le_coe.mpr hlt
  rw [msbOf_of_ne_zero h0, WithBotTop.coe_le_coe] at hM
  rw [msbOf_of_ne_zero h0, coe_add_coe, WithBotTop.coe_le_coe]
  omega
end Fpy.DigitBound
