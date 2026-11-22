-- Prove2me | solution 1 for Mpfx.isOdd_neighbor_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:21:42.338868+00:00
-- url     : https://prove2.me/submissions/8c00daa8-2003-48e8-a7e1-84daf4508378

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Rounding_Parity
import Theorems.Thm_Mpfx_neighbor_abs_le
import Theorems.Thm_Mpfx_Dyadic_coe_abs
import Theorems.Thm_Mpfx_Dyadic_coe_half
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_rat_abs
import Theorems.Thm_Mpfx_Dyadic_coe_rat_half
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_real_add
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_coe_real_mul
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_Dyadic_coe_real_sub
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_canonicalExp_mono
import Theorems.Thm_Mpfx_FiniteFormat_exp_le_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_isEven_zero
import Theorems.Thm_Mpfx_FiniteFormat_isOdd_iff_mem_shrink
import Theorems.Thm_Mpfx_FiniteFormat_ofIntZpow_mem_shrink_iff
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
import Theorems.Thm_Mpfx_abs_mul_two_zpow
import Theorems.Thm_Mpfx_canonicalExp_eq_of_log_eq
import Theorems.Thm_Mpfx_exp_le_canonicalExp_coe
import Theorems.Thm_Mpfx_log_eq_of_zpow_bounds
import Theorems.Thm_Mpfx_ofIntZpow_mem_unbounded
import Theorems.Thm_Mpfx_two_zpow_split_toNat
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


section
namespace Mpfx
private theorem two_zpow_log_le_neighbor {F : FiniteFormat} {x : ℝ} (hx : x ≠ 0)
    (hns : (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-F.canonicalExp x))
    {m : ℤ} (hm : m = ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ ∨
      m = ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) (hm0 : m ≠ 0) :
    (2 : ℝ) ^ Int.log 2 |x| ≤ |(m : ℝ) * (2 : ℝ) ^ F.canonicalExp x| := by
  set e := F.canonicalExp x
  set s := x * (2 : ℝ) ^ (-e)
  set L := Int.log 2 |x|
  have h2e : (0 : ℝ) < 2 ^ e := zpow_pos two_pos e
  rw [abs_mul_two_zpow]
  rcases lt_or_ge L e with hLe | hLe
  · have : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
    calc (2 : ℝ) ^ L ≤ 2 ^ e := zpow_le_zpow_right₀ (by norm_num) hLe.le
      _ ≤ |(m : ℝ)| * 2 ^ e := le_mul_of_one_le_left h2e.le this
  -- `N = 2^(L - e)` is an integer with `N ≤ |s|`, so `N ≤ |m|`.
  set N : ℤ := 2 ^ (L - e).toNat with hN_def
  have hNpos : 0 < N := by positivity
  have hN : (N : ℝ) * 2 ^ e = 2 ^ L := by
    rw [two_zpow_split_toNat (K := ℝ) hLe, hN_def]; push_cast; ring
  have hNs : (N : ℝ) ≤ |s| := by
    rw [abs_mul_two_zpow, ← mul_le_mul_iff_of_pos_right h2e, hN, mul_assoc,
      ← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero, mul_one]
    exact Int.zpow_log_le_self (by norm_num) (abs_pos.mpr hx)
  have hfl := Int.floor_le s
  have hlt : (⌊s⌋ : ℝ) < s := lt_of_le_of_ne hfl hns
  have hNm : N ≤ |m| := by
    rcases le_or_gt 0 s with hs | hs
    · rw [abs_of_nonneg hs] at hNs
      have : N ≤ ⌊s⌋ := Int.le_floor.mpr hNs
      rcases hm with rfl | rfl <;> rw [abs_of_nonneg (by omega)] <;> omega
    · rw [abs_of_neg hs] at hNs
      have : ⌊s⌋ < -N := by exact_mod_cast (show (⌊s⌋ : ℝ) < -N by linarith)
      rcases hm with rfl | rfl <;> rw [abs_of_neg (by omega)] <;> omega
  calc (2 : ℝ) ^ L = (N : ℝ) * 2 ^ e := hN.symm
    _ ≤ |(m : ℝ)| * 2 ^ e := mul_le_mul_of_nonneg_right (by exact_mod_cast hNm) h2e.le
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} (hp1 : F.p ≠ ((1 : ℕ) : Prec)) {x : ℝ}
    (h_lo_ne_s :
      (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-F.canonicalExp x))
    {m : ℤ} (hm : m = ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ ∨
      m = ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) :
    F.IsOdd (Dyadic.ofIntZpow m (F.canonicalExp x)) ↔ ¬ Even m := by
  have hx_ne : x ≠ 0 := fun hx0 => h_lo_ne_s (by simp [hx0])
  set e := F.canonicalExp x
  have hC := FiniteFormat.ofIntZpow_mem_shrink_iff F hp1 (exp_le_canonicalExp_coe F x)
    (fun _ hp => neighbor_abs_le x hm hp) fun hm0 => by
      have hlog := two_zpow_log_le_neighbor hx_ne h_lo_ne_s hm hm0
      rw [← Dyadic.coe_ofIntZpow] at hlog
      have h2L' : (0 : ℝ) < 2 ^ Int.log 2 |x| := zpow_pos two_pos _
      have h2L : (2 : ℝ) ^ Int.log 2 |x| ≠ 0 := h2L'.ne'
      calc e = F.canonicalExp ((2 : ℝ) ^ Int.log 2 |x|) := canonicalExp_eq_of_log_eq F hx_ne
            h2L (by rw [abs_of_pos h2L', log_eq_of_zpow_bounds h2L' le_rfl
              (zpow_lt_zpow_right₀ one_lt_two (lt_add_one _))])
        _ ≤ _ := F.canonicalExp_mono h2L (by rwa [abs_of_pos h2L'])
  have hmem : Dyadic.ofIntZpow m e ∈ F.unbounded :=
    ofIntZpow_mem_unbounded F (fun {e'} he' => F.exp_le_canonicalExp x he')
      (fun {_} hp => neighbor_abs_le x hm hp)
  exact (FiniteFormat.isOdd_iff_mem_shrink F hp1 _).trans
    ⟨fun h' => (not_congr hC).mp h'.2, fun h' => ⟨hmem, (not_congr hC).mpr h'⟩⟩
end Mpfx
