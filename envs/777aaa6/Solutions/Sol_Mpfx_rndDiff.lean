-- Prove2me | solution 1 for Mpfx.rndDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:46:02.839728+00:00
-- url     : https://prove2.me/submissions/3dc0fc68-4538-4fc8-9b51-c9295da995c5

import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Definitions.Def_Mpfx_DoubleRounding_Add
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
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_coe_real
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_anti
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe_real
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_sub
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_canonicalExp_mono
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_isEven_zero
import Theorems.Thm_Mpfx_FiniteFormat_mem_unbounded_of_mul_zpow_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_neg_mem
import Theorems.Thm_Mpfx_FiniteFormat_p_pos
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_isUndefined
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_p
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_unbounded
import Theorems.Thm_Mpfx_FiniteFormat_zero_mem
import Theorems.Thm_Mpfx_Format_boundAfterNext_top
import Theorems.Thm_Mpfx_Format_boundOK_neg_iff
import Theorems.Thm_Mpfx_Format_boundOK_zero
import Theorems.Thm_Mpfx_Format_finite_mem_values
import Theorems.Thm_Mpfx_Format_mem_unbounded_of_le
import Theorems.Thm_Mpfx_Format_neg_mem
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
import Theorems.Thm_Mpfx_Format_zero_mem
import Theorems.Thm_Mpfx_RoundsFinite_unique
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
import Theorems.Thm_Mpfx_canonicalExp_closed
import Theorems.Thm_Mpfx_canonicalExp_subnormal
import Theorems.Thm_Mpfx_eq_zero_of_coe_real_zero
import Theorems.Thm_Mpfx_exists_canonical_rep
import Theorems.Thm_Mpfx_exp_le_canonicalExp_coe
import Theorems.Thm_Mpfx_log_eq_of_zpow_bounds
import Theorems.Thm_Mpfx_nearest_error_le_half_ulp
import Theorems.Thm_Mpfx_rndDown_zero
import Theorems.Thm_Mpfx_rndExact
import Theorems.Thm_Mpfx_rndNeg
import Theorems.Thm_Mpfx_rndUp_zero
import Theorems.Thm_Mpfx_rnd_special
import Theorems.Thm_Mpfx_two_zpow_dbl
import Theorems.Thm_Mpfx_two_zpow_half
import Theorems.Thm_Mpfx_two_zpow_split_toNat
import Theorems.Thm_Mpfx_ulp_neg
import Theorems.Thm_Mpfx_ulp_of_ne_zero
import Theorems.Thm_P2M_Mpfx_nearest_eq_of_close__390f66b23c83
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
private theorem mem_F₂_of_subnormal {F₁ F₂ : FiniteFormat} {p₂ : ℕ}
    (hp₂ : F₂.p = (p₂ : Prec)) (hexp : F₂.exp ≤ F₁.exp)
    {v : Dyadic} (hqv : Dyadic.quantumAtLeast F₁.exp v)
    {e₂ : ℤ} (he₂ : F₂.exp = (e₂ : QExp))
    (hsub : Int.log 2 |(v : ℝ)| + 1 - (p₂ : ℤ) < e₂) : v ∈ F₂.unbounded := by
  by_cases hv0 : (v : ℝ) = 0
  · rw [eq_zero_of_coe_real_zero hv0]; exact FiniteFormat.zero_mem _
  -- Subnormal: the canonical exponent is the quantum `e₂`, a step `v` inherits.
  obtain ⟨C, hC⟩ := (Dyadic.quantumAtLeast_coe_real e₂ v).mp
    (Dyadic.quantumAtLeast_anti (he₂ ▸ hexp) hqv)
  exact F₂.mem_unbounded_of_mul_zpow_canonicalExp (m := C)
    (by rw [canonicalExp_subnormal hp₂ he₂ hv0 hsub.le]; exact hC)
private theorem mantissa_pos {c e : ℤ} {x : ℝ} (hxeq : x = (c : ℝ) * (2 : ℝ) ^ e)
    (hpos : 0 < x) : 0 < c := by
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have h : (0 : ℝ) < (c : ℝ) * (2 : ℝ) ^ e := hxeq ▸ hpos
  rcases mul_pos_iff.mp h with ⟨hc, _⟩ | ⟨_, hng⟩
  · exact_mod_cast hc
  · linarith
private theorem add_sub_mantissa_setup {F₁ : FiniteFormat} {p₁ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxpos : 0 < (x : ℝ)) (hypos : 0 < (y : ℝ)) (hyx : (y : ℝ) ≤ (x : ℝ))
    (hgap : F₁.canonicalExp (x : ℝ) - F₁.canonicalExp (y : ℝ) ≤ (p₁ : ℤ) + 1) :
    ∃ (cx cy : ℤ) (n : ℕ), 0 < cx ∧ 0 < cy ∧
      cx ≤ (2 : ℤ) ^ p₁ - 1 ∧ cy ≤ (2 : ℤ) ^ p₁ - 1 ∧
      (2 : ℤ) ^ n ≤ 2 * (2 : ℤ) ^ p₁ ∧
      (x : ℝ) = (cx : ℝ) * (2 : ℝ) ^ n * (2 : ℝ) ^ (F₁.canonicalExp (y : ℝ)) ∧
      (y : ℝ) = (cy : ℝ) * (2 : ℝ) ^ (F₁.canonicalExp (y : ℝ)) := by
  set ex := F₁.canonicalExp (x : ℝ) with hex
  set ey := F₁.canonicalExp (y : ℝ) with hey
  obtain ⟨cx, hcx_lt, hxeq⟩ := exists_canonical_rep F₁ hp₁ hx hxpos
  obtain ⟨cy, hcy_lt, hyeq⟩ := exists_canonical_rep F₁ hp₁ hy hypos
  rw [← hex] at hxeq; rw [← hey] at hyeq
  have hcx_pos : 0 < cx := mantissa_pos hxeq hxpos
  have hcy_pos : 0 < cy := mantissa_pos hyeq hypos
  have hey_le_ex : ey ≤ ex := by
    rw [hey, hex]
    exact FiniteFormat.canonicalExp_mono F₁ (ne_of_gt hypos)
      (by rw [abs_of_pos hypos, abs_of_pos hxpos]; exact hyx)
  set n : ℕ := (ex - ey).toNat with hn
  have hn_nat : n ≤ p₁ + 1 := by
    have : (n : ℤ) = ex - ey := by rw [hn, Int.toNat_of_nonneg (by omega)]
    omega
  have hsplit : (2 : ℝ) ^ ex = (2 : ℝ) ^ n * (2 : ℝ) ^ ey := by
    rw [hn]; exact two_zpow_split_toNat hey_le_ex
  have hcx_le : cx ≤ (2 : ℤ) ^ p₁ - 1 := by rw [abs_of_pos hcx_pos] at hcx_lt; omega
  have hcy_le : cy ≤ (2 : ℤ) ^ p₁ - 1 := by rw [abs_of_pos hcy_pos] at hcy_lt; omega
  have h2n_le : (2 : ℤ) ^ n ≤ 2 * (2 : ℤ) ^ p₁ := by
    calc (2 : ℤ) ^ n ≤ (2 : ℤ) ^ (p₁ + 1) := pow_le_pow_right₀ (by norm_num) hn_nat
      _ = 2 * (2 : ℤ) ^ p₁ := by rw [pow_succ]; ring
  exact ⟨cx, cy, n, hcx_pos, hcy_pos, hcx_le, hcy_le, h2n_le,
    by rw [hxeq, hsplit]; ring, hyeq⟩
private theorem two_pow_two_p_split {p₁ : ℕ} (hp : 0 < p₁) :
    (2 : ℤ) ≤ (2 : ℤ) ^ p₁ ∧
    (2 : ℤ) ^ (2 * p₁ + 1) = 2 * (2 : ℤ) ^ p₁ * (2 : ℤ) ^ p₁ := by
  refine ⟨?_, ?_⟩
  · calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p₁ := pow_le_pow_right₀ (by norm_num) hp
  · rw [show 2 * p₁ + 1 = p₁ + (p₁ + 1) from by ring, pow_add, pow_succ]; ring
private theorem addSub_precisionAtMost {F₁ : FiniteFormat} {p₁ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxpos : 0 < (x : ℝ)) (hypos : 0 < (y : ℝ)) (hyx : (y : ℝ) ≤ (x : ℝ))
    (hgap : F₁.canonicalExp (x : ℝ) - F₁.canonicalExp (y : ℝ) ≤ (p₁ : ℤ) + 1) :
    Dyadic.precisionAtMost ((2 * p₁ + 1 : ℕ) : Prec) (x + y) ∧
      Dyadic.precisionAtMost ((2 * p₁ + 1 : ℕ) : Prec) (x - y) := by
  obtain ⟨cx, cy, n, hcx_pos, hcy_pos, hcx_le, hcy_le, h2n_le, hx_rep, hy_rep⟩ :=
    add_sub_mantissa_setup hp₁ hx hy hxpos hypos hyx hgap
  obtain ⟨hAge, h2A2⟩ := two_pow_two_p_split (F₁.p_pos hp₁)
  have h2n_pos : (0 : ℤ) < (2 : ℤ) ^ n := by positivity
  have hprod : cx * (2 : ℤ) ^ n ≤ ((2 : ℤ) ^ p₁ - 1) * (2 * (2 : ℤ) ^ p₁) :=
    mul_le_mul hcx_le h2n_le h2n_pos.le (by omega)
  have hcxn_pos : 0 < cx * (2 : ℤ) ^ n := mul_pos hcx_pos h2n_pos
  -- `x ± y = (cx · 2^n ± cy) · 2^ey` with the coefficient below `2^(2p₁+1)`.
  set ey := F₁.canonicalExp (y : ℝ)
  refine ⟨(Dyadic.precisionAtMost_coe_real _ _).mpr ⟨cx * 2 ^ n + cy, ey, ?_, ?_⟩,
    (Dyadic.precisionAtMost_coe_real _ _).mpr ⟨cx * 2 ^ n - cy, ey, ?_, ?_⟩⟩
  · rw [Dyadic.coe_real_add, hx_rep, hy_rep]; push_cast; ring
  · rw [h2A2, abs_of_pos (by omega)]; nlinarith [hprod, hcy_le, hAge]
  · rw [Dyadic.coe_real_sub, hx_rep, hy_rep]; push_cast; ring
  · rw [h2A2, abs_lt]
    exact ⟨by nlinarith [hcxn_pos, hcy_le, hAge], by nlinarith [hprod, hcy_pos, hAge]⟩
private theorem gap_setup {F₁ : FiniteFormat} {p₁ : ℕ} (hp₁ : F₁.p = (p₁ : Prec))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxpos : 0 < (x : ℝ)) (hypos : 0 < (y : ℝ))
    (hgap : (p₁ : ℤ) + 1 < F₁.canonicalExp (x : ℝ) - F₁.canonicalExp (y : ℝ)) :
    ∃ cx : ℤ, (x : ℝ) = cx * 2 ^ F₁.canonicalExp (x : ℝ) ∧ 0 < cx ∧
      (cx : ℝ) ≤ 2 ^ (p₁ : ℤ) - 1 ∧
      F₁.canonicalExp (x : ℝ) = Int.log 2 (x : ℝ) + 1 - p₁ ∧
      F₁.exp ≤ ((Int.log 2 (x : ℝ) - p₁ : ℤ) : QExp) ∧
      (y : ℝ) ≤ 2 ^ (F₁.canonicalExp (y : ℝ) + p₁) - 2 ^ F₁.canonicalExp (y : ℝ) ∧
      (y : ℝ) < 2 ^ (F₁.canonicalExp (x : ℝ) - 2) := by
  set ex := F₁.canonicalExp (x : ℝ) with hex
  set ey := F₁.canonicalExp (y : ℝ) with hey
  obtain ⟨cx, hcx_lt, hxeq⟩ := exists_canonical_rep F₁ hp₁ hx hxpos
  obtain ⟨cy, hcy_lt, hyeq⟩ := exists_canonical_rep F₁ hp₁ hy hypos
  rw [← hex] at hxeq; rw [← hey] at hyeq
  have hcx_pos : 0 < cx := mantissa_pos hxeq hxpos
  have hcy_pos : 0 < cy := mantissa_pos hyeq hypos
  -- A positive significand below `2^p₁` is at most `2^p₁ − 1`.
  have hmant : ∀ {c : ℤ}, 0 < c → |c| < 2 ^ p₁ → (c : ℝ) ≤ 2 ^ (p₁ : ℤ) - 1 :=
      fun {c} hc h => by
    rw [abs_of_pos hc] at h
    have : c ≤ 2 ^ p₁ - 1 := by omega
    rw [zpow_natCast]; exact_mod_cast this
  -- `x` is normal: `2^ex ≤ x < 2^(⌊log₂ x⌋+1)` gives `ex ≤ ⌊log₂ x⌋`.
  have hex_le : ex ≤ Int.log 2 (x : ℝ) := by
    have hx_ge : (2 : ℝ) ^ ex ≤ (x : ℝ) := by
      rw [hxeq]
      have h1 : (1 : ℝ) ≤ (cx : ℝ) := by exact_mod_cast hcx_pos
      nlinarith [zpow_pos (show (0 : ℝ) < 2 by norm_num) ex]
    have hxlt : (x : ℝ) < (2 : ℝ) ^ (Int.log 2 (x : ℝ) + 1) :=
      Int.lt_zpow_succ_log_self (b := 2) (by norm_num) _
    by_contra hc
    have : (2 : ℝ) ^ (Int.log 2 (x : ℝ) + 1) ≤ (2 : ℝ) ^ ex :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  have hnorm : F₁.exp ≤ ((Int.log 2 (x : ℝ) - p₁ : ℤ) : QExp) :=
    le_trans (exp_le_canonicalExp_coe F₁ (y : ℝ)) (by
      rw [← hey]; exact_mod_cast (show ey ≤ Int.log 2 (x : ℝ) - p₁ by omega))
  have hex_val : ex = Int.log 2 (x : ℝ) + 1 - p₁ := by
    rw [hex, canonicalExp_closed hp₁ (ne_of_gt hxpos) (le_trans hnorm (by
      rw [abs_of_pos hxpos]; exact_mod_cast (show Int.log 2 (x : ℝ) - p₁ ≤
        Int.log 2 (x : ℝ) + 1 - p₁ by omega))), abs_of_pos hxpos]
  have h2ey : (0 : ℝ) < 2 ^ ey := zpow_pos (by norm_num) _
  have hy_le : (y : ℝ) ≤ 2 ^ (ey + p₁) - 2 ^ ey := by
    rw [hyeq, zpow_add₀ two_ne_zero, mul_comm ((2 : ℝ) ^ ey)]
    nlinarith [hmant hcy_pos hcy_lt]
  exact ⟨cx, hxeq, hcx_pos, hmant hcx_pos hcx_lt, hex_val, hnorm, hy_le,
    lt_of_lt_of_le (by linarith) (zpow_le_zpow_right₀ (by norm_num) (by omega))⟩
private theorem sub_key_bound {p₁ p₂ : ℕ} (hp : 0 < p₁) {k eb : ℤ}
    (hpp' : 2 * (p₁ : ℤ) + 1 ≤ (p₂ : ℤ))
    (hgap : eb + (p₁ : ℤ) ≤ k - (p₁ : ℤ) - 1)
    {b : ℝ} (hb_le : b ≤ (2 : ℝ) ^ (eb + (p₁ : ℤ)) - (2 : ℝ) ^ eb) :
    (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) + b < (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := by
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  have h2eb : (0 : ℝ) < (2 : ℝ) ^ eb := zpow_pos (by norm_num) _
  have hp₁ℤ : (1 : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast hp
  rcases lt_or_ge (k - (p₂ : ℤ) - 1) eb with hc | hc
  · -- `2^(k−p₂−1) < 2^eb`, so the `−2^eb` slack in `y`'s bound absorbs it.
    have h1 : (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) < (2 : ℝ) ^ eb :=
      zpow_lt_zpow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (eb + (p₁ : ℤ)) ≤ (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) :=
      zpow_le_zpow_right₀ (by norm_num) hgap
    linarith [hb_le, h1, h2]
  · -- `eb ≤ k−p₂−1`: `y < 2^(eb+p₁)` is tiny, and `2p₁+1 ≤ p₂` gives the margin.
    have hb_lt : b < (2 : ℝ) ^ (eb + (p₁ : ℤ)) := by linarith [h2eb]
    have h3 : (2 : ℝ) ^ (eb + (p₁ : ℤ)) ≤ (2 : ℝ) ^ (k - (p₂ : ℤ) - 1 + (p₁ : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hsplit : (2 : ℝ) ^ (k - (p₂ : ℤ) - 1 + (p₁ : ℤ))
        = (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) * (2 : ℝ) ^ (p₁ : ℤ) := by rw [← zpow_add₀ hne]
    have h2p1 : (1 : ℝ) ≤ (2 : ℝ) ^ (p₁ : ℤ) := by
      rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℤ) from (zpow_zero 2).symm]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h6 : (1 : ℝ) + (2 : ℝ) ^ (p₁ : ℤ) ≤ (2 : ℝ) ^ ((p₁ : ℤ) + 1) := by
      rw [zpow_add₀ hne, zpow_one]; nlinarith [h2p1]
    have hfinal : (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) + (2 : ℝ) ^ (k - (p₂ : ℤ) - 1 + (p₁ : ℤ))
        ≤ (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := by
      rw [hsplit]
      calc (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) + (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) * (2 : ℝ) ^ (p₁ : ℤ)
          = (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) * (1 + (2 : ℝ) ^ (p₁ : ℤ)) := by ring
        _ ≤ (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) * (2 : ℝ) ^ ((p₁ : ℤ) + 1) :=
            mul_le_mul_of_nonneg_left h6 (le_of_lt (zpow_pos (by norm_num) _))
        _ = (2 : ℝ) ^ (k - (p₂ : ℤ) - 1 + ((p₁ : ℤ) + 1)) := by rw [← zpow_add₀ hne]
        _ ≤ (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith [hb_lt, h3, hfinal]
private theorem rndSub_pos_normal {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ + 1 ≤ p₂)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxpos : 0 < (x : ℝ)) (hypos : 0 < (y : ℝ)) (hyx : (y : ℝ) < (x : ℝ))
    (hgap : (p₁ : ℤ) + 1 < F₁.canonicalExp (x : ℝ) - F₁.canonicalExp (y : ℝ))
    (hF2norm : F₂.exp ≤ ((Int.log 2 |((x - y : Dyadic) : ℝ)| + 1 - (p₂ : ℤ) : ℤ) : QExp))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((x - y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((x - y : Dyadic) : ℝ) w := by
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  have hp₁ℤ : (1 : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast F₁.p_pos hp₁
  have hpp' : (2 * (p₁ : ℤ) + 1) ≤ (p₂ : ℤ) := by omega
  have hr_real : ((x - y : Dyadic) : ℝ) = (x : ℝ) - (y : ℝ) := by push_cast; ring
  have hrpos : 0 < ((x - y : Dyadic) : ℝ) := by rw [hr_real]; linarith
  have hr_ne : ((x - y : Dyadic) : ℝ) ≠ 0 := ne_of_gt hrpos
  have pow_half := two_zpow_half
  have pow_dbl := two_zpow_dbl
  set ex := F₁.canonicalExp (x : ℝ) with hex
  set ey := F₁.canonicalExp (y : ℝ) with hey
  obtain ⟨cx, hxeq, hcx_pos, hcx_le, hex_val, hnormF1, hy_le, hy_lt⟩ :=
    gap_setup hp₁ hx hy hxpos hypos hgap
  set k := Int.log 2 (x : ℝ) with hk
  rw [show ex - 2 = k - (p₁ : ℤ) - 1 by omega] at hy_lt
  have hgap_key : ey + (p₁ : ℤ) ≤ k - (p₁ : ℤ) - 1 := by omega
  -- binade of `x`
  have hx_lo : (2 : ℝ) ^ k ≤ (x : ℝ) := Int.zpow_log_le_self (b := 2) (by norm_num) hxpos
  have hx_hi : (x : ℝ) < (2 : ℝ) ^ (k + 1) := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) _
  -- precision-exponent `canonicalExp` for any `F₁`-normal value, binade `≥ k−1`
  have cE1 : ∀ v : ℝ, v ≠ 0 → k - 1 ≤ Int.log 2 |v| →
      F₁.canonicalExp v = Int.log 2 |v| + 1 - (p₁ : ℤ) := by
    intro v hv hlog
    refine canonicalExp_closed hp₁ hv (le_trans hnormF1 ?_)
    exact_mod_cast (show k - (p₁ : ℤ) ≤ Int.log 2 |v| + 1 - (p₁ : ℤ) by omega)
  -- `x` is a multiple of `2^ex` and (doubling the mantissa) of `2^(ex−1)`
  have hquant_x_ex : Dyadic.quantumAtLeast (ex : QExp) x :=
    (Dyadic.quantumAtLeast_coe_real ex x).mpr ⟨cx, hxeq⟩
  have hquant_x_ex1 : Dyadic.quantumAtLeast ((ex - 1 : ℤ) : QExp) x :=
    (Dyadic.quantumAtLeast_coe_real (ex - 1) x).mpr ⟨2 * cx, by
      rw [hxeq, pow_dbl ex]; push_cast; ring⟩
  have hu₁ : ¬ (F₁.unbounded).IsUndefined (.nearest tb₁) := by
    rw [FiniteFormat.unbounded_isUndefined]; exact hundef₁
  by_cases hbot : (x : ℝ) = (2 : ℝ) ^ k
  · -- Sub-case 2b: `x = 2^k`, `x − y` drops a binade.
    have h2ex2_le : (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) ≤ (2 : ℝ) ^ (k - 2) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hr_lt : ((x - y : Dyadic) : ℝ) < (2 : ℝ) ^ k := by rw [hr_real, hbot]; linarith [hypos]
    have hr_gt : (2 : ℝ) ^ (k - 1) ≤ ((x - y : Dyadic) : ℝ) := by
      rw [hr_real, hbot]
      have e1 : (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ (k - 1) := pow_dbl k
      have e2 : (2 : ℝ) ^ (k - 1) = 2 * (2 : ℝ) ^ (k - 2) := by
        rw [pow_dbl (k - 1), show (k - 1) - 1 = k - 2 from by ring]
      have hylt2 : (y : ℝ) < (2 : ℝ) ^ (k - 2) := lt_of_lt_of_le hy_lt h2ex2_le
      linarith [e1, e2, hylt2]
    have hlogr : Int.log 2 ((x - y : Dyadic) : ℝ) = k - 1 :=
      log_eq_of_zpow_bounds hrpos hr_gt (by rwa [sub_add_cancel])
    have hcE2r : F₂.canonicalExp ((x - y : Dyadic) : ℝ) = k - (p₂ : ℤ) := by
      rw [canonicalExp_closed hp₂ hr_ne hF2norm, abs_of_pos hrpos, hlogr]; ring
    have herr : |(z : ℝ) - ((x - y : Dyadic) : ℝ)| ≤ (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) := by
      have hh := nearest_error_le_half_ulp hz
      rw [ulp_of_ne_zero F₂ hr_ne, hcE2r] at hh
      rwa [pow_half (k - (p₂ : ℤ))] at hh
    have hrx_abs : |((x - y : Dyadic) : ℝ) - (x : ℝ)| = (y : ℝ) := by
      rw [hr_real, abs_of_nonpos (show (x : ℝ) - (y : ℝ) - (x : ℝ) ≤ 0 by linarith)]; ring
    have hzx_close : |(z : ℝ) - (x : ℝ)| < (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := by
      have htri := abs_sub_le (z : ℝ) ((x - y : Dyadic) : ℝ) (x : ℝ)
      rw [hrx_abs] at htri
      have hkey := sub_key_bound (F₁.p_pos hp₁) hpp' hgap_key hy_le
      linarith [htri, herr, hkey]
    -- `◦₁(x−y) = x`
    have hcE1r : F₁.canonicalExp ((x - y : Dyadic) : ℝ) = ex - 1 := by
      rw [cE1 _ hr_ne (by rw [abs_of_pos hrpos]; omega), abs_of_pos hrpos, hlogr]; omega
    have e4 : (2 : ℝ) ^ (ex - 1) / 2 = (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := by
      rw [pow_half (ex - 1)]; congr 1; omega
    have hrx_round : RoundsFinite F₁.unbounded (.nearest tb₁) ((x - y : Dyadic) : ℝ) x := by
      refine nearest_eq_of_close' F₁ tb₁ _ hundef₁ (by rw [hcE1r]; exact hquant_x_ex1) ?_
      rw [hcE1r, hrx_abs, e4]; exact hy_lt
    -- `◦₁(z) = x` (splitting on whether `z` is below or above `2^k`)
    have hzx_round : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) x := by
      rw [abs_lt] at hzx_close
      have hz_gt : (2 : ℝ) ^ (k - 1) < (z : ℝ) := by
        have hlow : (x : ℝ) - (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) < (z : ℝ) := by linarith [hzx_close.1]
        rw [hbot] at hlow
        have e1 : (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ (k - 1) := pow_dbl k
        have e2 : (2 : ℝ) ^ (k - 1) = 2 * (2 : ℝ) ^ (k - 2) := by
          rw [pow_dbl (k - 1), show (k - 1) - 1 = k - 2 from by ring]
        linarith [hlow, h2ex2_le, e1, e2]
      have hz_pos : 0 < (z : ℝ) := lt_trans (zpow_pos (by norm_num) _) hz_gt
      rcases lt_or_ge (z : ℝ) ((2 : ℝ) ^ k) with hzlt | hzge
      · -- `z < 2^k`: binade `k−1`
        have hlogz : Int.log 2 (z : ℝ) = k - 1 :=
          log_eq_of_zpow_bounds hz_pos hz_gt.le (by rwa [sub_add_cancel])
        have hcE1z : F₁.canonicalExp (z : ℝ) = ex - 1 := by
          rw [cE1 _ (ne_of_gt hz_pos) (by rw [abs_of_pos hz_pos]; omega),
            abs_of_pos hz_pos, hlogz]; omega
        refine nearest_eq_of_close' F₁ tb₁ _ hundef₁ (by rw [hcE1z]; exact hquant_x_ex1) ?_
        rw [hcE1z, e4, abs_lt]
        exact ⟨by linarith [hzx_close.1], by linarith [hzx_close.2]⟩
      · -- `z ≥ 2^k`: binade `k`
        have hz_hi : (z : ℝ) < (2 : ℝ) ^ (k + 1) := by
          have hhigh : (z : ℝ) < (x : ℝ) + (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := by
            linarith [hzx_close.2]
          rw [hbot] at hhigh
          have e1 : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
            rw [zpow_add₀ hne, zpow_one]; ring
          have hb2 : (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) ≤ (2 : ℝ) ^ k :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
          linarith [hhigh, e1, hb2, zpow_pos (show (0 : ℝ) < 2 by norm_num) k]
        have hlogz : Int.log 2 (z : ℝ) = k := log_eq_of_zpow_bounds hz_pos hzge hz_hi
        have hcE1z : F₁.canonicalExp (z : ℝ) = ex := by
          rw [cE1 _ (ne_of_gt hz_pos) (by rw [abs_of_pos hz_pos]; omega),
            abs_of_pos hz_pos, hlogz]; omega
        refine nearest_eq_of_close' F₁ tb₁ _ hundef₁ (by rw [hcE1z]; exact hquant_x_ex) ?_
        rw [hcE1z]
        have e5 : (2 : ℝ) ^ ex / 2 = (2 : ℝ) ^ (ex - 1) := pow_half ex
        have hb3 : (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) < (2 : ℝ) ^ (ex - 1) :=
          zpow_lt_zpow_right₀ (by norm_num) (by omega)
        rw [e5, abs_lt]
        exact ⟨by linarith [hzx_close.1, hb3], by linarith [hzx_close.2, hb3]⟩
    have hw_eq : w = x := RoundsFinite.unique hu₁ hw hzx_round
    rw [hw_eq]; exact hrx_round
  · -- Sub-case 2a: `2^k < x`, `x − y` stays in `x`'s binade.
    have hbot' : (2 : ℝ) ^ k < (x : ℝ) := lt_of_le_of_ne hx_lo (fun h => hbot h.symm)
    have hexk : ex ≤ k := by omega
    set d : ℕ := (k - ex).toNat
    have hd : (d : ℤ) = k - ex := Int.toNat_of_nonneg (by omega)
    have hsplitk : (2 : ℝ) ^ k = (2 : ℝ) ^ (d : ℤ) * (2 : ℝ) ^ ex := by
      rw [← zpow_add₀ hne]; congr 1; omega
    have h2d_real : (2 : ℝ) ^ (d : ℤ) = ((2 : ℤ) ^ d : ℝ) := by simp [zpow_natCast]
    have hk_eq : (2 : ℝ) ^ k = ((2 : ℤ) ^ d : ℝ) * (2 : ℝ) ^ ex := by
      rw [← h2d_real]; exact hsplitk
    have h2ex : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos (by norm_num) _
    have hcx_gt : (2 : ℤ) ^ d < cx := by
      have hltR : ((2 : ℤ) ^ d : ℝ) < (cx : ℝ) := by
        have hlt : ((2 : ℤ) ^ d : ℝ) * (2 : ℝ) ^ ex < (cx : ℝ) * (2 : ℝ) ^ ex := by
          rw [← hxeq, ← hk_eq]; exact hbot'
        exact lt_of_mul_lt_mul_right hlt (le_of_lt h2ex)
      exact_mod_cast hltR
    have hx_ge : (2 : ℝ) ^ k + (2 : ℝ) ^ ex ≤ (x : ℝ) := by
      have hcx_ge1 : ((2 : ℤ) ^ d : ℝ) + 1 ≤ (cx : ℝ) := by
        have : (2 : ℤ) ^ d + 1 ≤ cx := by omega
        exact_mod_cast this
      rw [hxeq, hk_eq]; nlinarith [hcx_ge1, h2ex]
    have hx_max : (x : ℝ) ≤ (2 : ℝ) ^ (k + 1) - (2 : ℝ) ^ ex := by
      rw [hxeq]
      have hsplit : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (p₁ : ℤ) * (2 : ℝ) ^ ex := by
        rw [← zpow_add₀ hne]; congr 1; omega
      rw [hsplit]; nlinarith [hcx_le, h2ex]
    have hr_lo : (2 : ℝ) ^ k < ((x - y : Dyadic) : ℝ) := by
      rw [hr_real]
      have hb1 : (y : ℝ) < (2 : ℝ) ^ ex :=
        lt_trans hy_lt (zpow_lt_zpow_right₀ (by norm_num) (by omega))
      linarith [hx_ge, hb1]
    have hr_hi : ((x - y : Dyadic) : ℝ) < (2 : ℝ) ^ (k + 1) := by
      rw [hr_real]; linarith [hx_hi, hypos]
    have hlogr : Int.log 2 ((x - y : Dyadic) : ℝ) = k :=
      log_eq_of_zpow_bounds hrpos (le_of_lt hr_lo) hr_hi
    have hcE1r : F₁.canonicalExp ((x - y : Dyadic) : ℝ) = ex := by
      rw [cE1 _ hr_ne (by rw [abs_of_pos hrpos]; omega), abs_of_pos hrpos, hlogr]; omega
    have hcE2r : F₂.canonicalExp ((x - y : Dyadic) : ℝ) = k + 1 - (p₂ : ℤ) := by
      rw [canonicalExp_closed hp₂ hr_ne hF2norm, abs_of_pos hrpos, hlogr]
    have herr : |(z : ℝ) - ((x - y : Dyadic) : ℝ)| ≤ (2 : ℝ) ^ (k - (p₂ : ℤ)) := by
      have hh := nearest_error_le_half_ulp hz
      rw [ulp_of_ne_zero F₂ hr_ne, hcE2r] at hh
      have e3 : (2 : ℝ) ^ (k + 1 - (p₂ : ℤ)) / 2 = (2 : ℝ) ^ (k - (p₂ : ℤ)) := by
        rw [show k + 1 - (p₂ : ℤ) = (k - (p₂ : ℤ)) + 1 from by ring, zpow_add₀ hne, zpow_one]
        ring
      rwa [e3] at hh
    have hrx_abs : |((x - y : Dyadic) : ℝ) - (x : ℝ)| = (y : ℝ) := by
      rw [hr_real, abs_of_nonpos (show (x : ℝ) - (y : ℝ) - (x : ℝ) ≤ 0 by linarith)]; ring
    have hexm1 : (2 : ℝ) ^ (ex - 1) = (2 : ℝ) ^ (k - (p₁ : ℤ)) := by congr 1; omega
    have hzx_close : |(z : ℝ) - (x : ℝ)| < (2 : ℝ) ^ (ex - 1) := by
      have htri := abs_sub_le (z : ℝ) ((x - y : Dyadic) : ℝ) (x : ℝ)
      rw [hrx_abs] at htri
      have hb1 : (2 : ℝ) ^ (k - (p₂ : ℤ)) ≤ (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hd2 : (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) + (2 : ℝ) ^ (k - (p₁ : ℤ) - 1)
          = (2 : ℝ) ^ (k - (p₁ : ℤ)) := by
        rw [pow_dbl (k - (p₁ : ℤ))]; ring
      rw [hexm1]; linarith [htri, herr, hb1, hy_lt, hd2]
    have hrx_round : RoundsFinite F₁.unbounded (.nearest tb₁) ((x - y : Dyadic) : ℝ) x := by
      refine nearest_eq_of_close' F₁ tb₁ _ hundef₁ (by rw [hcE1r]; exact hquant_x_ex) ?_
      rw [hcE1r, hrx_abs]
      have e5 : (2 : ℝ) ^ ex / 2 = (2 : ℝ) ^ (ex - 1) := pow_half ex
      rw [e5]
      calc (y : ℝ) < (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := hy_lt
        _ < (2 : ℝ) ^ (ex - 1) := by
            rw [hexm1]; exact zpow_lt_zpow_right₀ (by norm_num) (by omega)
    have hzx_round : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) x := by
      rw [abs_lt] at hzx_close
      have e8 : (2 : ℝ) ^ ex = 2 * (2 : ℝ) ^ (ex - 1) := pow_dbl ex
      have h2ex1 : (0 : ℝ) < (2 : ℝ) ^ (ex - 1) := zpow_pos (by norm_num) _
      have hz_gt : (2 : ℝ) ^ k < (z : ℝ) := by
        have hlow : (x : ℝ) - (2 : ℝ) ^ (ex - 1) < (z : ℝ) := by linarith [hzx_close.1]
        linarith [hlow, hx_ge, e8, h2ex1]
      have hz_pos : 0 < (z : ℝ) := lt_trans (zpow_pos (by norm_num) _) hz_gt
      have hz_hi : (z : ℝ) < (2 : ℝ) ^ (k + 1) := by
        have hhigh : (z : ℝ) < (x : ℝ) + (2 : ℝ) ^ (ex - 1) := by linarith [hzx_close.2]
        linarith [hhigh, hx_max, e8]
      have hlogz : Int.log 2 (z : ℝ) = k := log_eq_of_zpow_bounds hz_pos (le_of_lt hz_gt) hz_hi
      have hcE1z : F₁.canonicalExp (z : ℝ) = ex := by
        rw [cE1 _ (ne_of_gt hz_pos) (by rw [abs_of_pos hz_pos]; omega),
          abs_of_pos hz_pos, hlogz]; omega
      refine nearest_eq_of_close' F₁ tb₁ _ hundef₁ (by rw [hcE1z]; exact hquant_x_ex) ?_
      rw [hcE1z]
      have e5 : (2 : ℝ) ^ ex / 2 = (2 : ℝ) ^ (ex - 1) := pow_half ex
      rw [e5, abs_lt]; exact ⟨hzx_close.1, hzx_close.2⟩
    have hw_eq : w = x := RoundsFinite.unique hu₁ hw hzx_round
    rw [hw_eq]; exact hrx_round
private theorem rnd_of_cases {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₂ : F₂.p = (p₂ : Prec)) (hpp : 2 * p₁ + 1 ≤ p₂) (hexp : F₂.exp ≤ F₁.exp)
    {r : Dyadic} (hquant_r : Dyadic.quantumAtLeast F₁.exp r) {small : Prop}
    (hsmall : small → Dyadic.precisionAtMost ((2 * p₁ + 1 : ℕ) : Prec) r)
    {z w : Dyadic}
    (hmid : ¬ small → F₂.exp ≤ ((Int.log 2 |(r : ℝ)| + 1 - (p₂ : ℤ) : ℤ) : QExp) →
      RoundsFinite F₁.unbounded (.nearest tb₁) (r : ℝ) w)
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) (r : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) (r : ℝ) w := by
  by_cases hs : small
  · exact rndExact (F₂ := F₂.unbounded)
      (Format.mem_unbounded_of_le (p := ((2 * p₁ + 1 : ℕ) : Prec)) (e := F₁.exp)
        (by rw [hp₂]; exact ENat.coe_le_coe.mpr hpp) hexp (hsmall hs) hquant_r) hz hw
  by_cases hF2norm : F₂.exp ≤ ((Int.log 2 |(r : ℝ)| + 1 - (p₂ : ℤ) : ℤ) : QExp)
  · exact hmid hs hF2norm
  -- Subnormal in `F₂`: `F₂.exp` is finite and above the precision exponent.
  obtain ⟨e₂, he₂⟩ : ∃ e : ℤ, F₂.exp = (e : QExp) := by
    cases h : F₂.exp using QExp.recBotCoe with
    | bot => exact absurd (h ▸ bot_le) hF2norm
    | coe e => exact ⟨e, rfl⟩
  rw [he₂] at hF2norm
  exact rndExact (F₂ := F₂.unbounded) (mem_F₂_of_subnormal hp₂ hexp hquant_r he₂
    (not_le.mp fun hc => hF2norm (by exact_mod_cast hc))) hz hw
private theorem rndSub_pos {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ + 1 ≤ p₂)
    (hexp : F₂.exp ≤ F₁.exp)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxpos : 0 < (x : ℝ)) (hypos : 0 < (y : ℝ)) (hyx : (y : ℝ) < (x : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((x - y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((x - y : Dyadic) : ℝ) w :=
  rnd_of_cases hp₂ hpp hexp (Dyadic.quantumAtLeast_sub hx.2.1 hy.2.1)
    (fun h => (addSub_precisionAtMost hp₁ hx hy hxpos hypos hyx.le h).2)
    (fun h hn => rndSub_pos_normal hp₁ hp₂ hpp hundef₁ hx hy hxpos hypos hyx
      (not_le.mp h) hn hz hw) hz hw
private theorem mem_F₂_unbounded {F₁ F₂ : FiniteFormat} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec))
    (hexp : F₂.exp ≤ F₁.exp) (hp1p2 : p₁ ≤ p₂)
    {d : Dyadic} (hd : d ∈ F₁) : d ∈ F₂.unbounded :=
  Format.mem_unbounded_of_le (p := F₁.p) (e := F₁.exp)
    (by rw [hp₁, hp₂]; exact ENat.coe_le_coe.mpr hp1p2) hexp hd.1 hd.2.1
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ + 1 ≤ p₂)
    (hexp : F₂.exp ≤ F₁.exp)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {a b : Dyadic} (ha : a ∈ F₁) (hb : b ∈ F₁)
    (hann : 0 ≤ (a : ℝ)) (hbnn : 0 ≤ (b : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((a - b : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((a - b : Dyadic) : ℝ) w := by
  have hp1p2 : p₁ ≤ p₂ := by omega
  by_cases hab_mem : (a - b : Dyadic) ∈ F₁
  · -- `a − b` is representable in `F₁` (a zero operand, or `a = b`): exact.
    exact rndExact (mem_F₂_unbounded hp₁ hp₂ hexp hp1p2 hab_mem) hz hw
  · -- otherwise `a > 0`, `b > 0`, `a ≠ b`.
    have hane : (a : ℝ) ≠ 0 := by
      intro h; apply hab_mem
      have hd : a = 0 := eq_zero_of_coe_real_zero h
      rw [hd, show (0 - b : Dyadic) = -b from by ring]; exact FiniteFormat.neg_mem hb
    have hbne : (b : ℝ) ≠ 0 := by
      intro h; apply hab_mem
      have hd : b = 0 := eq_zero_of_coe_real_zero h
      rw [hd, show (a - 0 : Dyadic) = a from by ring]; exact ha
    have habne : (a : ℝ) ≠ (b : ℝ) := by
      intro h; apply hab_mem
      have hd : a = b := (Dyadic.coe_real_inj a b).mp h
      rw [hd, show (b - b : Dyadic) = 0 from by ring]; exact FiniteFormat.zero_mem F₁
    have hap : 0 < (a : ℝ) := lt_of_le_of_ne hann (Ne.symm hane)
    have hbp : 0 < (b : ℝ) := lt_of_le_of_ne hbnn (Ne.symm hbne)
    have hnegval : -((a - b : Dyadic) : ℝ) = ((b - a : Dyadic) : ℝ) := by push_cast; ring
    rcases lt_or_gt_of_ne habne with hab | hab
    · -- `a < b`: negate to `b − a > 0` and apply `rndSub_pos`.
      refine rndNeg hz hw (fun hz' hw' => ?_)
      rw [hnegval] at hz' ⊢
      exact rndSub_pos hp₁ hp₂ hpp hexp hundef₁ hb ha hbp hap hab hz' hw'
    · -- `a > b`: apply `rndSub_pos` directly.
      exact rndSub_pos hp₁ hp₂ hpp hexp hundef₁ ha hb hap hbp hab hz hw
end Mpfx
