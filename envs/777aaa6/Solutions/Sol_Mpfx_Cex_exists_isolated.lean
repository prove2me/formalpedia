-- Prove2me | solution 1 for Mpfx.Cex.exists_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:46:03.363081+00:00
-- url     : https://prove2.me/submissions/55af04c9-578e-4cb0-b2c9-14db2139d246

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Theorems.Thm_Mpfx_Dyadic_coe_abs
import Theorems.Thm_Mpfx_Dyadic_coe_half
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_rat_abs
import Theorems.Thm_Mpfx_Dyadic_coe_rat_half
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_real_add
import Theorems.Thm_Mpfx_Dyadic_coe_real_eq_ratCast
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_coe_real_mul
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_Dyadic_coe_real_sub
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_ext_real
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_canonicalExp_mono
import Theorems.Thm_Mpfx_FiniteFormat_exists_mul_zpow_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_isEven_zero
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_isUndefined
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_p
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_boundAfterNext_top
import Theorems.Thm_Mpfx_Format_boundOK_neg_iff
import Theorems.Thm_Mpfx_Format_boundOK_zero
import Theorems.Thm_Mpfx_Format_finite_mem_values
import Theorems.Thm_Mpfx_Format_special_mem_values
import Theorems.Thm_Mpfx_Format_unbounded_b
import Theorems.Thm_Mpfx_Format_unbounded_exp
import Theorems.Thm_Mpfx_Format_unbounded_p
import Theorems.Thm_Mpfx_Format_unbounded_specials
import Theorems.Thm_Mpfx_Format_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_withBound_b
import Theorems.Thm_Mpfx_Format_withBound_exp
import Theorems.Thm_Mpfx_Format_withBound_p
import Theorems.Thm_Mpfx_Format_withBound_specials
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
import Theorems.Thm_Mpfx_rndDown_zero
import Theorems.Thm_Mpfx_rndUp_zero
import Theorems.Thm_Mpfx_rnd_special
import Theorems.Thm_Mpfx_two_zpow_shift
import Theorems.Thm_Mpfx_ulp_neg
attribute [local simp] Mpfx.Dyadic.coe_abs
attribute [local simp] Mpfx.Dyadic.coe_half
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_rat_abs
attribute [local simp] Mpfx.Dyadic.coe_rat_half
attribute [local simp] Mpfx.Dyadic.coe_rat_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_real_add
attribute [local simp] Mpfx.Dyadic.coe_real_inj
attribute [local simp] Mpfx.Dyadic.coe_real_mul
attribute [local simp] Mpfx.Dyadic.coe_real_neg
attribute [local simp] Mpfx.Dyadic.coe_real_sub
attribute [local simp] Mpfx.Dyadic.coe_real_zero
attribute [local simp] Mpfx.Dyadic.precisionAtMost_neg_iff
attribute [local simp] Mpfx.Dyadic.precisionAtMost_top
attribute [local simp] Mpfx.Dyadic.quantumAtLeast_bot
attribute [local simp] Mpfx.Dyadic.quantumAtLeast_neg_iff
attribute [local simp] Mpfx.FiniteFormat.IsEven.neg_iff
attribute [local simp] Mpfx.FiniteFormat.IsOdd.neg_iff
attribute [local simp] Mpfx.FiniteFormat.extend_toFormat
attribute [local simp] Mpfx.FiniteFormat.isEven_zero
attribute [local simp] Mpfx.FiniteFormat.unbounded_b
attribute [local simp] Mpfx.FiniteFormat.unbounded_canonicalExp
attribute [local simp] Mpfx.FiniteFormat.unbounded_exp
attribute [local simp] Mpfx.FiniteFormat.unbounded_isUndefined
attribute [local simp] Mpfx.FiniteFormat.unbounded_p
attribute [local simp] Mpfx.FiniteFormat.unbounded_toFormat
attribute [local simp] Mpfx.FiniteFormat.unbounded_unbounded
attribute [local simp] Mpfx.Format.boundAfterNext_top
attribute [local simp] Mpfx.Format.boundOK_neg_iff
attribute [local simp] Mpfx.Format.boundOK_zero
attribute [local simp] Mpfx.Format.finite_mem_values
attribute [local simp] Mpfx.Format.special_mem_values
attribute [local simp] Mpfx.Format.unbounded_b
attribute [local simp] Mpfx.Format.unbounded_exp
attribute [local simp] Mpfx.Format.unbounded_p
attribute [local simp] Mpfx.Format.unbounded_specials
attribute [local simp] Mpfx.Format.unbounded_unbounded
attribute [local simp] Mpfx.Format.withBound_b
attribute [local simp] Mpfx.Format.withBound_exp
attribute [local simp] Mpfx.Format.withBound_p
attribute [local simp] Mpfx.Format.withBound_specials
attribute [local simp] Mpfx.Special.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_finite
attribute [local simp] Mpfx.WithSpecial.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_special
attribute [local simp] Mpfx.WithSpecial.toReal_finite
attribute [local simp] Mpfx.WithSpecial.toReal_special
attribute [local simp] Mpfx.rndDown_zero
attribute [local simp] Mpfx.rndUp_zero
attribute [local simp] Mpfx.rnd_special
attribute [local simp] Mpfx.ulp_neg


section
namespace Mpfx
namespace Cex
private theorem exists_mul_zpow_of_le (c : ℤ) {a K : ℤ} (h : K ≤ a) :
    ∃ n : ℤ, (c : ℝ) * (2 : ℝ) ^ a = (n : ℝ) * (2 : ℝ) ^ K := by
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h)
  refine ⟨c * 2 ^ k, ?_⟩
  rw [show a = K + k by omega, zpow_add₀ two_ne_zero, zpow_natCast]
  push_cast; ring
end Cex
end Mpfx
end

set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
theorem _root_.solution (F : FiniteFormat) {m : Dyadic} (hm : (m : ℝ) ≠ 0) :
    ∃ K : ℤ, Isolated F m K := by
  obtain ⟨cm, j, hcm⟩ := m.property
  have hm_eq : (m : ℝ) = (cm : ℝ) * (2 : ℝ) ^ j := by
    rw [Dyadic.coe_real_eq_ratCast, hcm]; push_cast; ring
  set E : ℤ := Int.log 2 |(m : ℝ)| - 1 with hE
  have hmE : (2 : ℝ) ^ (E + 1) ≤ |(m : ℝ)| := by
    rw [hE, sub_add_cancel]
    exact Int.zpow_log_le_self (b := 2) (by norm_num) (abs_pos.mpr hm)
  -- Values of magnitude at least `2^E` are multiples of `2^k`, the step at `2^E`.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ∀ v ∈ F.unbounded, (2 : ℝ) ^ E ≤ |(v : ℝ)| →
      ∃ c : ℤ, (v : ℝ) = (c : ℝ) * (2 : ℝ) ^ k := by
    refine ⟨F.canonicalExp ((2 : ℝ) ^ E), fun v hv hvE => ?_⟩
    obtain ⟨c, hc⟩ := F.exists_mul_zpow_canonicalExp hv
    have hmono : F.canonicalExp ((2 : ℝ) ^ E) ≤ F.canonicalExp (v : ℝ) :=
      F.canonicalExp_mono (zpow_pos two_pos E).ne' (by rwa [abs_of_pos (zpow_pos two_pos E)])
    exact ⟨_, hc.trans (two_zpow_shift c hmono)⟩
  refine ⟨min (min j k) E, fun v hv hlt => ?_⟩
  set K := min (min j k) E
  have hKE : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ E := zpow_le_zpow_right₀ (by norm_num) (min_le_right _ _)
  have hE1 : (2 : ℝ) ^ (E + 1) = 2 * (2 : ℝ) ^ E := by rw [zpow_add_one₀ two_ne_zero]; ring
  -- `v` is within `2^E` of `m`, so `|v| ≥ 2^E`.
  have hvE : (2 : ℝ) ^ E ≤ |(v : ℝ)| := by
    have := abs_sub_abs_le_abs_sub (m : ℝ) v
    rw [abs_sub_comm] at this
    linarith
  obtain ⟨cv, hcv⟩ := hk v hv hvE
  obtain ⟨n₁, hn₁⟩ := exists_mul_zpow_of_le cv
    (show K ≤ k from (min_le_left _ _).trans (min_le_right _ _))
  obtain ⟨n₂, hn₂⟩ := exists_mul_zpow_of_le cm
    (show K ≤ j from (min_le_left _ _).trans (min_le_left _ _))
  have hdiff : (v : ℝ) - m = ((n₁ - n₂ : ℤ) : ℝ) * (2 : ℝ) ^ K := by
    rw [hcv, hm_eq, hn₁, hn₂]; push_cast; ring
  rw [hdiff, abs_mul, abs_of_pos (zpow_pos two_pos K : (0 : ℝ) < 2 ^ K)] at hlt
  have h0 : n₁ - n₂ = 0 := by
    have h1 : |((n₁ - n₂ : ℤ) : ℝ)| < 1 := (mul_lt_iff_lt_one_left (zpow_pos two_pos K)).mp hlt
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast h1)
  apply Dyadic.ext_real
  have : (v : ℝ) - m = 0 := by rw [hdiff, h0]; simp
  linarith
end Mpfx.Cex
