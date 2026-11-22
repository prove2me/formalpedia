-- Prove2me | solution 1 for Mpfx.rndAdd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:53:39.350783+00:00
-- url     : https://prove2.me/submissions/f61f9875-fe81-40f8-8e89-e0c012928904

import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Definitions.Def_Mpfx_DoubleRounding_Add
import Theorems.Thm_Mpfx_rndDiff
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
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_add
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_anti
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe_real
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
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
import Theorems.Thm_Mpfx_IsFaithfulRound_mul_nonneg
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
import Theorems.Thm_Mpfx_canonicalExp_closed
import Theorems.Thm_Mpfx_canonicalExp_eq_of_log_eq
import Theorems.Thm_Mpfx_canonicalExp_subnormal
import Theorems.Thm_Mpfx_eq_zero_of_coe_real_zero
import Theorems.Thm_Mpfx_exists_canonical_rep
import Theorems.Thm_Mpfx_exp_le_canonicalExp_coe
import Theorems.Thm_Mpfx_log_eq_of_zpow_bounds
import Theorems.Thm_Mpfx_rndDown_eq
import Theorems.Thm_Mpfx_rndDown_zero
import Theorems.Thm_Mpfx_rndExact
import Theorems.Thm_Mpfx_rndNeg
import Theorems.Thm_Mpfx_rndUp_zero
import Theorems.Thm_Mpfx_rnd_special
import Theorems.Thm_Mpfx_two_zpow_split_toNat
import Theorems.Thm_Mpfx_ulp_neg
import Theorems.Thm_Mpfx_ulp_of_ne_zero
import Theorems.Thm_P2M_Mpfx_rnd_lt_mid__f8e65c434f46
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
private theorem rndAdd_pos_normal {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ + 1 ≤ p₂)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxpos : 0 < (x : ℝ)) (hypos : 0 < (y : ℝ))
    (hgap : (p₁ : ℤ) + 1 < F₁.canonicalExp (x : ℝ) - F₁.canonicalExp (y : ℝ))
    (hF2norm : F₂.exp ≤ ((Int.log 2 |((x + y : Dyadic) : ℝ)| + 1 - (p₂ : ℤ) : ℤ) : QExp))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((x + y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((x + y : Dyadic) : ℝ) w := by
  have hxypos : 0 < ((x + y : Dyadic) : ℝ) := by rw [Dyadic.coe_real_add]; linarith
  set ex := F₁.canonicalExp (x : ℝ) with hex
  set ey := F₁.canonicalExp (y : ℝ) with hey
  have hp₁ℤ : (1 : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast F₁.p_pos hp₁
  have hpp' : (2 * (p₁ : ℤ) + 1) ≤ (p₂ : ℤ) := by omega
  obtain ⟨cx, hxeq, -, hcx_le, hex_val, -, -, hy_lt⟩ := gap_setup hp₁ hx hy hxpos hypos hgap
  have hlogx : Int.log 2 (x : ℝ) = ex + (p₁ : ℤ) - 1 := by omega
  -- binade bounds on `x`, and `x ≤ 2^(ex+p₁) − 2^ex`
  have hx_lo : (2 : ℝ) ^ (ex + (p₁ : ℤ) - 1) ≤ (x : ℝ) := by
    rw [← hlogx]; exact Int.zpow_log_le_self (b := 2) (by norm_num) hxpos
  have h2ex : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos (by norm_num) _
  have hx_le : (x : ℝ) ≤ (2 : ℝ) ^ (ex + (p₁ : ℤ)) - (2 : ℝ) ^ ex := by
    rw [hxeq, zpow_add₀ two_ne_zero, mul_comm ((2 : ℝ) ^ ex)]
    nlinarith [hcx_le, h2ex]
  -- `x + y` is in `x`'s binade: `2^(ex+p₁-1) ≤ x+y < 2^(ex+p₁)`
  have hxy_lo : (2 : ℝ) ^ (ex + (p₁ : ℤ) - 1) ≤ ((x + y : Dyadic) : ℝ) := by
    rw [Dyadic.coe_real_add]; linarith
  have h2ex2_lt : (2 : ℝ) ^ (ex - 2) < (2 : ℝ) ^ ex :=
    zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have hxy_hi : ((x + y : Dyadic) : ℝ) < (2 : ℝ) ^ (ex + (p₁ : ℤ)) := by
    rw [Dyadic.coe_real_add]; linarith [hx_le, hy_lt, h2ex2_lt]
  have hlogxy : Int.log 2 ((x + y : Dyadic) : ℝ) = ex + (p₁ : ℤ) - 1 :=
    log_eq_of_zpow_bounds hxypos hxy_lo (by rwa [sub_add_cancel])
  -- canonicalExp of `x+y` in `F₁` and `F₂`
  have hcexp₁xy : F₁.canonicalExp ((x + y : Dyadic) : ℝ) = ex := by
    rw [hex]
    exact canonicalExp_eq_of_log_eq F₁ (ne_of_gt hxypos) (ne_of_gt hxpos)
      (by rw [abs_of_pos hxypos, abs_of_pos hxpos, hlogxy, hlogx])
  have hcexp₂xy : F₂.canonicalExp ((x + y : Dyadic) : ℝ) = ex + (p₁ : ℤ) - (p₂ : ℤ) := by
    rw [canonicalExp_closed hp₂ (ne_of_gt hxypos) hF2norm, abs_of_pos hxypos, hlogxy]; ring
  -- rndDown F₁ (x+y) has real value x
  have hrdxy : (rndDown F₁ ((x + y : Dyadic) : ℝ) : ℝ) = (x : ℝ) := by
    rw [rndDown_eq, Dyadic.coe_ofIntZpow, hcexp₁xy]
    have h2negex : (0 : ℝ) < (2 : ℝ) ^ (-ex) := zpow_pos (by norm_num) _
    have hxscaled : ((cx : ℝ) * (2 : ℝ) ^ ex) * (2 : ℝ) ^ (-ex) = (cx : ℝ) := by
      rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; simp
    have hyscaled : (y : ℝ) * (2 : ℝ) ^ (-ex) < 1 := by
      have heq : (2 : ℝ) ^ (ex - 2) * (2 : ℝ) ^ (-ex) = (2 : ℝ) ^ (-2 : ℤ) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
      have h14 : (2 : ℝ) ^ (-2 : ℤ) < 1 := by norm_num
      nlinarith [mul_lt_mul_of_pos_right hy_lt h2negex, heq, h14]
    have hfloor : ⌊((x + y : Dyadic) : ℝ) * (2 : ℝ) ^ (-ex)⌋ = cx := by
      rw [Int.floor_eq_iff]
      refine ⟨?_, ?_⟩
      · rw [Dyadic.coe_real_add, hxeq]
        nlinarith [hxscaled, mul_nonneg (le_of_lt hypos) (le_of_lt h2negex)]
      · rw [Dyadic.coe_real_add, hxeq]
        nlinarith [hyscaled, hxscaled]
    rw [hfloor, hxeq]
  -- assemble the `rnd_lt_mid'` hypotheses
  apply rnd_lt_mid' hundef₁ hxypos ?_ ?_ ?_ hz hw
  · rw [hcexp₁xy, hcexp₂xy]; omega
  · rw [hcexp₁xy, hlogxy]; omega
  · -- x+y < midp F₁ (x+y) - ulp F₂ (x+y) / 2
    have hmidp : midp F₁ ((x + y : Dyadic) : ℝ) = (x : ℝ) + (2 : ℝ) ^ ex / 2 := by
      rw [midp, ulp_of_ne_zero F₁ hxypos.ne', hrdxy, hcexp₁xy]
    have hulp₂ : ulp F₂ ((x + y : Dyadic) : ℝ) = (2 : ℝ) ^ (ex + (p₁ : ℤ) - (p₂ : ℤ)) := by
      rw [ulp_of_ne_zero F₂ hxypos.ne', hcexp₂xy]
    rw [hmidp, hulp₂, Dyadic.coe_real_add]
    -- y < 2^ex/2 - 2^(ex+p₁-p₂)/2
    have hu2_le : (2 : ℝ) ^ (ex + (p₁ : ℤ) - (p₂ : ℤ)) ≤ (2 : ℝ) ^ (ex - 2) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2ex2 : (2 : ℝ) ^ (ex - 2) = (2 : ℝ) ^ ex / 4 := by
      rw [show ex - 2 = ex + (-2 : ℤ) from by ring, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),
          show (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 from by norm_num]
      ring
    linarith [hy_lt, hu2_le, h2ex2, h2ex]
private theorem rndAdd_pos {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ + 1 ≤ p₂)
    (hexp : F₂.exp ≤ F₁.exp)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxpos : 0 < (x : ℝ)) (hypos : 0 < (y : ℝ)) (hyx : (y : ℝ) ≤ (x : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((x + y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((x + y : Dyadic) : ℝ) w :=
  rnd_of_cases hp₂ hpp hexp (Dyadic.quantumAtLeast_add hx.2.1 hy.2.1)
    (fun h => (addSub_precisionAtMost hp₁ hx hy hxpos hypos hyx h).1)
    (fun h hn => rndAdd_pos_normal hp₁ hp₂ hpp hundef₁ hx hy hxpos hypos
      (not_le.mp h) hn hz hw) hz hw
private theorem mem_F₂_unbounded {F₁ F₂ : FiniteFormat} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec))
    (hexp : F₂.exp ≤ F₁.exp) (hp1p2 : p₁ ≤ p₂)
    {d : Dyadic} (hd : d ∈ F₁) : d ∈ F₂.unbounded :=
  Format.mem_unbounded_of_le (p := F₁.p) (e := F₁.exp)
    (by rw [hp₁, hp₂]; exact ENat.coe_le_coe.mpr hp1p2) hexp hd.1 hd.2.1
private theorem rndAdd_nonneg {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ + 1 ≤ p₂)
    (hexp : F₂.exp ≤ F₁.exp)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxnn : 0 ≤ (x : ℝ)) (hynn : 0 ≤ (y : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((x + y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((x + y : Dyadic) : ℝ) w := by
  have hp1p2 : p₁ ≤ p₂ := by omega
  rcases eq_or_lt_of_le hxnn with hx0 | hxp
  · -- x = 0
    have hxd : x = 0 :=
      eq_zero_of_coe_real_zero hx0.symm
    rw [hxd, zero_add] at hz ⊢
    exact rndExact (mem_F₂_unbounded hp₁ hp₂ hexp hp1p2 hy) hz hw
  · rcases eq_or_lt_of_le hynn with hy0 | hyp
    · -- y = 0
      have hyd : y = 0 :=
        eq_zero_of_coe_real_zero hy0.symm
      rw [hyd, add_zero] at hz ⊢
      exact rndExact (mem_F₂_unbounded hp₁ hp₂ hexp hp1p2 hx) hz hw
    · rcases le_total (y : ℝ) (x : ℝ) with hyx | hxy
      · exact rndAdd_pos hp₁ hp₂ hpp hexp hundef₁ hx hy hxp hyp hyx hz hw
      · rw [show (x + y : Dyadic) = y + x from add_comm x y] at hz ⊢
        exact rndAdd_pos hp₁ hp₂ hpp hexp hundef₁ hy hx hyp hxp hxy hz hw
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
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((x + y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((x + y : Dyadic) : ℝ) w := by
  rcases (lt_or_ge (x : ℝ) 0).symm with hxnn | hxneg
  · rcases (lt_or_ge (y : ℝ) 0).symm with hynn | hyneg
    · -- both nonnegative
      exact rndAdd_nonneg hp₁ hp₂ hpp hexp hundef₁ hx hy hxnn hynn hz hw
    · -- `x ≥ 0 > y`: `x + y = x − (−y)`
      have hb : (-y) ∈ F₁ := FiniteFormat.neg_mem hy
      have hbnn : 0 ≤ ((-y : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
      rw [show (x + y : Dyadic) = x - (-y) from by ring] at hz ⊢
      exact rndDiff hp₁ hp₂ hpp hexp hundef₁ hx hb hxnn hbnn hz hw
  · rcases (lt_or_ge (y : ℝ) 0).symm with hynn | hyneg
    · -- `x < 0 ≤ y`: `x + y = y − (−x)`
      have hb : (-x) ∈ F₁ := FiniteFormat.neg_mem hx
      have hbnn : 0 ≤ ((-x : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
      rw [show (x + y : Dyadic) = y - (-x) from by ring] at hz ⊢
      exact rndDiff hp₁ hp₂ hpp hexp hundef₁ hy hb hynn hbnn hz hw
    · -- both nonpositive: joint negation reduces to `rndAdd_nonneg`
      have hnx : (-x) ∈ F₁ := FiniteFormat.neg_mem hx
      have hny : (-y) ∈ F₁ := FiniteFormat.neg_mem hy
      have hnxnn : 0 ≤ ((-x : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
      have hnynn : 0 ≤ ((-y : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
      have hnegval : -((x + y : Dyadic) : ℝ) = (((-x) + (-y) : Dyadic) : ℝ) := by push_cast; ring
      refine rndNeg hz hw (fun hz' hw' => ?_)
      rw [hnegval] at hz' ⊢
      exact rndAdd_nonneg hp₁ hp₂ hpp hexp hundef₁ hnx hny hnxnn hnynn hz' hw'
end Mpfx
