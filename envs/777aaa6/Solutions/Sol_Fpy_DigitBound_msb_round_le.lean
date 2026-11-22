-- Prove2me | solution 1 for Fpy.DigitBound.msb_round_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:22:29.131846+00:00
-- url     : https://prove2.me/submissions/ff172ecc-0cc2-4c70-ae7a-de35902d29d3

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
import Theorems.Thm_Fpy_DigitBound_LsbAt_le
import Theorems.Thm_Fpy_DigitBound_msbOf_le_coe
import Theorems.Thm_Fpy_DigitBound_msbOf_of_ne_zero
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_FiniteFormat_zpow_mem_unbounded
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
import Theorems.Thm_Mpfx_abs_faithful_le_of_le
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow



set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}
namespace Fpy.DigitBound
theorem _root_.solution {F : FiniteFormat} {rm : RoundingMode} {x : ℝ} {y : Mpfx.Dyadic}
    (hy : RoundsFinite F.unbounded rm x y) (hx : x ≠ 0) {k : ℤ} (hk : F.exp ≤ (k : QExp)) :
    msbOf (.finite (y : ℝ)) ≤ ((max (Int.log 2 |x| + 1) k : ℤ) : EInt) := by
  set j := max (Int.log 2 |x| + 1) k
  have hN := F.zpow_mem_unbounded (j := j) (hk.trans (by exact_mod_cast le_max_right _ _))
  have hxN : |x| ≤ ((Dyadic.ofIntZpow 1 j : Mpfx.Dyadic) : ℝ) := by
    rw [Dyadic.coe_ofIntZpow, Int.cast_one, one_mul]
    exact (msbOf_le_coe.mp (msbOf_of_ne_zero hx).le).le.trans
      (zpow_le_zpow_right₀ (by norm_num) (le_max_left _ _))
  have hyN := abs_faithful_le_of_le hN hxN hy.isFaithfulRound
  rw [Dyadic.coe_ofIntZpow, Int.cast_one, one_mul] at hyN
  refine msbOf_le_coe.mpr (hyN.trans_lt ?_)
  exact zpow_lt_zpow_right₀ (by norm_num) (by omega)
end Fpy.DigitBound
