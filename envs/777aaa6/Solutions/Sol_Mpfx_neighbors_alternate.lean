-- Prove2me | solution 1 for Mpfx.neighbors_alternate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:23:56.76023+00:00
-- url     : https://prove2.me/submissions/bc6ccb8c-6790-4d29-9934-3fcda77de44a

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Rounding_Parity
import Theorems.Thm_Mpfx_neighbor_abs_le
import Theorems.Thm_Mpfx_isOdd_neighbor_iff
import Theorems.Thm_Mpfx_Dyadic_IsRepresentableAtP_ne_zero
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
import Theorems.Thm_Mpfx_Dyadic_ext_real
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_ne_zero
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_exp_le_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_isEven_zero
import Theorems.Thm_Mpfx_FiniteFormat_isOdd_ofIntZpow_of_p_one
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
import Theorems.Thm_Mpfx_canonicalExp_expFinite
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



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} (x : ℝ)
    (h : ¬ F.IsUndefined .toOdd)
    (h_lo_ne_s :
      (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-F.canonicalExp x)) :
    F.IsOdd (Dyadic.ofIntZpow (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) (F.canonicalExp x))
      ↔ ¬ F.IsOdd
        (Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ (F.canonicalExp x)) := by
  have hx_ne : x ≠ 0 := fun hx0 => h_lo_ne_s (by simp [hx0])
  set e := F.canonicalExp x
  set s := x * (2 : ℝ) ^ (-e)
  set k := ⌊s⌋
  by_cases hp1 : F.p = ((1 : ℕ) : Prec)
  swap
  · rw [isOdd_neighbor_iff hp1 h_lo_ne_s (Or.inl rfl), isOdd_neighbor_iff hp1 h_lo_ne_s
      (Or.inr rfl), Int.even_add_one, not_not]
  -- `p = 1`: the values are `0` and `±2^j`, and parity counts `j` from `exp`.
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : ℤ, F.exp = (e₀ : QExp) := by
    cases hexp : F.exp using QExp.recBotCoe with
    | bot => exact absurd ⟨hp1, hexp, Or.inl rfl⟩ h
    | coe e₀ => exact ⟨e₀, rfl⟩
  have he : e₀ ≤ e := F.exp_le_canonicalExp x he₀
  have hpow : ∀ σ j : ℤ, |σ| = 1 → e₀ ≤ j →
      (F.IsOdd (Dyadic.ofIntZpow σ j) ↔ Even (j - e₀)) := fun σ j hσ hj =>
    F.isOdd_ofIntZpow_of_p_one hp1 he₀ hσ hj
  have hdbl : ∀ σ : ℤ, Dyadic.ofIntZpow (2 * σ) e = Dyadic.ofIntZpow σ (e + 1) := fun σ =>
    Dyadic.ext_real (by
      simp only [Dyadic.coe_ofIntZpow]; rw [zpow_add_one₀ two_ne_zero]; push_cast; ring)
  have hzero : Dyadic.ofIntZpow 0 e = 0 := Dyadic.ext_real (by simp)
  -- A neighbour `0` puts `x` below `2^e`, so `e` is the quantum.
  have hsub : (k = 0 ∨ k = -1) → e = e₀ := by
    intro hk01
    have hfl : (k : ℝ) ≤ s := Int.floor_le s
    have hlt : s < k + 1 := Int.lt_floor_add_one s
    have hs_lt : |s| < 1 := by
      rcases hk01 with h0 | h0 <;> rw [h0] at hfl hlt <;> push_cast at hfl hlt
      · exact abs_lt.mpr ⟨by linarith, by linarith⟩
      · have : s ≠ -1 := fun hs => h_lo_ne_s (by rw [h0, hs]; push_cast; ring)
        exact abs_lt.mpr ⟨lt_of_le_of_ne hfl (Ne.symm this), by linarith⟩
    have hx_lt : |x| < 2 ^ e := by
      have h2e : (0 : ℝ) < 2 ^ e := zpow_pos two_pos e
      have : |s| * 2 ^ e = |x| := by
        rw [abs_mul_two_zpow, mul_assoc, ← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero,
          mul_one]
      nlinarith
    have hL : Int.log 2 |x| < e := (Int.lt_zpow_iff_log_lt (by norm_num) (abs_pos.mpr hx_ne)).mp
      (by exact_mod_cast hx_lt)
    have := canonicalExp_expFinite hp1 he₀ hx_ne
    push_cast at this
    omega
  have hk_bnd : |k| ≤ 2 ^ 1 := neighbor_abs_le x (Or.inl rfl) hp1
  have hk1_bnd : |k + 1| ≤ 2 ^ 1 := neighbor_abs_le x (Or.inr rfl) hp1
  rw [abs_le] at hk_bnd hk1_bnd
  have hk_range : k = -2 ∨ k = -1 ∨ k = 0 ∨ k = 1 := by norm_num at hk_bnd hk1_bnd; omega
  rcases hk_range with hk' | hk' | hk' | hk' <;> rw [hk']
  · rw [show (-2 : ℤ) = 2 * -1 by norm_num, hdbl, show 2 * (-1 : ℤ) + 1 = -1 by norm_num,
      hpow (-1) (e + 1) (by norm_num) (by omega), hpow (-1) e (by norm_num) he,
      show e + 1 - e₀ = e - e₀ + 1 by ring, Int.even_add_one, not_not]
  · rw [show (-1 : ℤ) + 1 = 0 by norm_num, hzero, hpow (-1) e (by norm_num) he,
      hsub (Or.inr hk'), sub_self]
    exact iff_of_false (fun h' => h'.ne_zero rfl) (not_not.mpr Even.zero)
  · rw [zero_add, hzero, hpow 1 e (by norm_num) he, hsub (Or.inl hk'), sub_self]
    exact iff_of_true Even.zero (fun h' => h'.ne_zero rfl)
  · rw [show (1 : ℤ) + 1 = 2 * 1 by norm_num, hdbl, hpow 1 (e + 1) (by norm_num) (by omega),
      hpow 1 e (by norm_num) he, show e + 1 - e₀ = e - e₀ + 1 by ring, Int.even_add_one]
end Mpfx
