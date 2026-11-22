-- Prove2me | solution 1 for Mpfx.rndSqrt_expBot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:54:48.311178+00:00
-- url     : https://prove2.me/submissions/5aedebda-76ff-4883-8533-cd152fea5e89

import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Definitions.Def_Mpfx_DoubleRounding_Sqrt
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
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_isEven_zero
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
import Theorems.Thm_Mpfx_canonicalExp_expBot
import Theorems.Thm_Mpfx_exists_canonical_rep
import Theorems.Thm_Mpfx_rndDown_add_ulp_le
import Theorems.Thm_Mpfx_rndDown_eq
import Theorems.Thm_Mpfx_rndDown_le
import Theorems.Thm_Mpfx_rndDown_zero
import Theorems.Thm_Mpfx_rndExact
import Theorems.Thm_Mpfx_rndUp_zero
import Theorems.Thm_Mpfx_rnd_special
import Theorems.Thm_Mpfx_round_round_mid_cases
import Theorems.Thm_Mpfx_two_zpow_half
import Theorems.Thm_Mpfx_ulp_neg
import Theorems.Thm_Mpfx_ulp_of_ne_zero
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
private theorem log_sqrt_bounds {x : ℝ} (hx : 0 < x) :
    2 * Int.log 2 (Real.sqrt x) ≤ Int.log 2 x ∧
      Int.log 2 x ≤ 2 * Int.log 2 (Real.sqrt x) + 1 := by
  set L := Int.log 2 (Real.sqrt x) with hL
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  -- `2^L ≤ √x < 2^(L+1)` (definition of `Int.log`)
  have hlo : (2 : ℝ) ^ L ≤ Real.sqrt x := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) hsx
    rw [← hL] at this; exact_mod_cast this
  have hhi : Real.sqrt x < (2 : ℝ) ^ (L + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) (Real.sqrt x)
    rw [← hL] at this; exact_mod_cast this
  -- square: `2^(2L) ≤ x < 2^(2L+2)`
  have hx_lo : (2 : ℝ) ^ (2 * L) ≤ x := by
    have he : ((2 : ℝ) ^ L) ^ 2 = (2 : ℝ) ^ (2 * L) := by
      rw [pow_two, ← zpow_add₀ hne]; congr 1; ring
    have h : ((2 : ℝ) ^ L) ^ 2 ≤ (Real.sqrt x) ^ 2 := by gcongr
    rw [he, hsq] at h; exact h
  have hx_hi : x < (2 : ℝ) ^ (2 * L + 2) := by
    have he : ((2 : ℝ) ^ (L + 1)) ^ 2 = (2 : ℝ) ^ (2 * L + 2) := by
      rw [pow_two, ← zpow_add₀ hne]; congr 1; ring
    have h : (Real.sqrt x) ^ 2 < ((2 : ℝ) ^ (L + 1)) ^ 2 := by gcongr
    rw [hsq, he] at h; exact h
  -- read off `Int.log 2 x`
  have h1 : 2 * L ≤ Int.log 2 x :=
    (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hx).mp (by exact_mod_cast hx_lo)
  have h2 : Int.log 2 x < 2 * L + 2 :=
    (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hx).mp (by exact_mod_cast hx_hi)
  omega
private theorem round_round_sqrt_aux {F₁ F₂ : FiniteFormat} {x : ℝ} (hx : 0 < x)
    (hxrep : ∃ mx : ℤ, x = (mx : ℝ) * (2 : ℝ) ^ (F₁.canonicalExp x))
    (hf1 : 2 * F₁.canonicalExp (Real.sqrt x) ≤ F₁.canonicalExp x)
    (hle : F₁.canonicalExp (Real.sqrt x) ≤ Int.log 2 (Real.sqrt x) + 1)
    (hquant : F₂.canonicalExp (Real.sqrt x) + Int.log 2 (Real.sqrt x) + 1
                ≤ 2 * F₁.canonicalExp (Real.sqrt x) - 2) :
    ulp F₂ (Real.sqrt x) / 2 < |Real.sqrt x - midp F₁ (Real.sqrt x)| := by
  set s := Real.sqrt x
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hx
  have hsq : s ^ 2 = x := Real.sq_sqrt hx.le
  set e₁ := F₁.canonicalExp s with he₁
  set e₂ := F₂.canonicalExp s with he₂
  set k := Int.log 2 s with hk
  have he₂_le : e₂ ≤ e₁ - 2 := by omega
  have hu1_pos : (0 : ℝ) < (2 : ℝ) ^ e₁ := zpow_pos (by norm_num) _
  have hu2_pos : (0 : ℝ) < (2 : ℝ) ^ e₂ := zpow_pos (by norm_num) _
  -- binade of `s`
  have hk_hi : s < (2 : ℝ) ^ (k + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) s
    rw [← hk] at this; exact_mod_cast this
  -- `a = rndDown₁ s = ma · 2^e₁`
  set ma : ℤ := ⌊s * (2 : ℝ) ^ (-e₁)⌋ with hma
  set a : ℝ := (ma : ℝ) * (2 : ℝ) ^ e₁ with ha
  have ha_eq : (rndDown F₁ s : ℝ) = a := by
    rw [rndDown_eq, Dyadic.coe_ofIntZpow, ← he₁, ← hma]
  have hma_nonneg : 0 ≤ ma := Int.floor_nonneg.mpr (by positivity)
  have ha_nonneg : 0 ≤ a := by
    rw [ha]; exact mul_nonneg (by exact_mod_cast hma_nonneg) hu1_pos.le
  have ha_le : a ≤ s := ha_eq ▸ rndDown_le F₁ s
  have hk_hi_a : a < (2 : ℝ) ^ (k + 1) := lt_of_le_of_lt ha_le hk_hi
  -- make `ma`/`a` opaque so later `linarith`/`ring` don't unfold `⌊·⌋`
  clear_value ma a
  -- `a + u₁ ≤ 2^(k+1)` (the round-down plus its ulp stays under the binade top)
  have ha_top : a + (2 : ℝ) ^ e₁ ≤ (2 : ℝ) ^ (k + 1) := by
    have h := rndDown_add_ulp_le F₁ hs_pos hle
    rwa [ha_eq, ulp_of_ne_zero F₁ hs_pos.ne'] at h
  -- `u₂ ≤ u₁/2`
  have hu2_le_half : (2 : ℝ) ^ e₂ ≤ (2 : ℝ) ^ e₁ / 2 := by
    have h1 : (2 : ℝ) ^ e₂ ≤ (2 : ℝ) ^ (e₁ - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith [h1, two_zpow_half e₁]
  -- quantitative bound `u₂·2^(k+1) ≤ u₁²/4`
  have hqbound : (2 : ℝ) ^ e₂ * (2 : ℝ) ^ (k + 1) ≤ ((2 : ℝ) ^ e₁) ^ 2 / 4 := by
    have h1 : (2 : ℝ) ^ e₂ * (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (e₂ + (k + 1)) := by
      rw [← zpow_add₀ hne]
    have h2 : (2 : ℝ) ^ (e₂ + (k + 1)) ≤ (2 : ℝ) ^ (2 * e₁ - 2) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h3 : (2 : ℝ) ^ (2 * e₁ - 2) = ((2 : ℝ) ^ e₁) ^ 2 / 4 := by
      rw [show (2 * e₁ - 2 : ℤ) = e₁ + e₁ + (-2) from by ring, zpow_add₀ hne, zpow_add₀ hne,
          show (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 from by norm_num, pow_two]; ring
    rw [h1]; linarith [h2, h3]
  by_contra hcon
  rw [not_lt] at hcon
  have hmidp : midp F₁ s = a + (2 : ℝ) ^ e₁ / 2 := by
    rw [midp, ulp_of_ne_zero F₁ hs_pos.ne', ha_eq, ← he₁]
  rw [show ulp F₂ s = (2 : ℝ) ^ e₂ from by rw [ulp_of_ne_zero F₂ hs_pos.ne', ← he₂],
    hmidp, abs_le] at hcon
  -- `a + ½(u₁−u₂) ≤ s ≤ a + ½(u₁+u₂)`
  have hsl : a + ((2 : ℝ) ^ e₁ - (2 : ℝ) ^ e₂) / 2 ≤ s := by linarith [hcon.1]
  have hsr : s ≤ a + ((2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₂) / 2 := by linarith [hcon.2]
  have hb_nonneg : 0 ≤ a + ((2 : ℝ) ^ e₁ - (2 : ℝ) ^ e₂) / 2 := by
    have : (2 : ℝ) ^ e₂ ≤ (2 : ℝ) ^ e₁ := zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith [ha_nonneg]
  -- square to bound `x`
  have hlow : (a + ((2 : ℝ) ^ e₁ - (2 : ℝ) ^ e₂) / 2) ^ 2 ≤ x := by
    rw [← hsq]; gcongr
  have hupp : x ≤ (a + ((2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₂) / 2) ^ 2 := by
    rw [← hsq]; gcongr
  set A : ℝ := a ^ 2 + (2 : ℝ) ^ e₁ * a with hAdef
  set M : ℝ := (2 : ℝ) ^ (2 * e₁) with hMdef
  have hMpos : (0 : ℝ) < M := zpow_pos (by norm_num) _
  have hMu1 : M = ((2 : ℝ) ^ e₁) ^ 2 := by
    rw [hMdef, pow_two, show (2 * e₁ : ℤ) = e₁ + e₁ from by ring, zpow_add₀ hne]
  clear_value A M
  -- lower / upper separations
  have hHl' : (2 : ℝ) ^ e₂ * a < (((2 : ℝ) ^ e₁ - (2 : ℝ) ^ e₂) / 2) ^ 2 := by
    have haU : a + (2 : ℝ) ^ e₁ / 2 < (2 : ℝ) ^ (k + 1) := by linarith [ha_top, hu1_pos]
    have hbound1 : (2 : ℝ) ^ e₂ * (a + (2 : ℝ) ^ e₁ / 2) < ((2 : ℝ) ^ e₁) ^ 2 / 4 := by
      have := mul_lt_mul_of_pos_left haU hu2_pos
      linarith [this, hqbound]
    nlinarith [hbound1, sq_nonneg ((2 : ℝ) ^ e₂)]
  have hbound2 : (2 : ℝ) ^ e₂ * a < ((2 : ℝ) ^ e₁) ^ 2 / 4 := by
    have := mul_lt_mul_of_pos_left hk_hi_a hu2_pos
    linarith [this, hqbound]
  have hIII : (2 : ℝ) ^ e₂ * a + (((2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₂) / 2) ^ 2 < M := by
    rw [hMu1]
    nlinarith [hbound2, hu2_le_half, hu1_pos, hu2_pos]
  -- `A < x < A + M`
  have hpos : A < x := by
    have e : (a + ((2 : ℝ) ^ e₁ - (2 : ℝ) ^ e₂) / 2) ^ 2
        = A - (2 : ℝ) ^ e₂ * a + (((2 : ℝ) ^ e₁ - (2 : ℝ) ^ e₂) / 2) ^ 2 := by rw [hAdef]; ring
    linarith [hlow, hHl', e]
  have hupp'x : x < A + M := by
    have e : (a + ((2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₂) / 2) ^ 2
        = A + ((2 : ℝ) ^ e₂ * a + (((2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₂) / 2) ^ 2) := by rw [hAdef]; ring
    linarith [hupp, hIII, e]
  -- divisibility: `A` and `x` are integer multiples of `M = 2^(2e₁)`
  have hAeq : A = ((ma * (ma + 1) : ℤ) : ℝ) * M := by
    rw [hAdef, ha, hMdef, show (2 * e₁ : ℤ) = e₁ + e₁ from by ring, zpow_add₀ hne]
    push_cast; ring
  have hxdvis : ∃ X : ℤ, x = (X : ℝ) * M := by
    obtain ⟨mx, hmx⟩ := hxrep
    have hd : (0 : ℤ) ≤ F₁.canonicalExp x - 2 * e₁ := by omega
    refine ⟨mx * 2 ^ (F₁.canonicalExp x - 2 * e₁).toNat, ?_⟩
    have key : ((mx * 2 ^ (F₁.canonicalExp x - 2 * e₁).toNat : ℤ) : ℝ) * M
        = (mx : ℝ) * (2 : ℝ) ^ F₁.canonicalExp x := by
      rw [hMdef]; push_cast
      rw [mul_assoc, ← zpow_natCast (2 : ℝ) (F₁.canonicalExp x - 2 * e₁).toNat,
          Int.toNat_of_nonneg hd, ← zpow_add₀ hne,
          show (F₁.canonicalExp x - 2 * e₁) + 2 * e₁ = F₁.canonicalExp x from by ring]
    rw [key]; exact hmx
  obtain ⟨X, hX⟩ := hxdvis
  rw [hAeq, hX] at hpos hupp'x
  have h1 : ma * (ma + 1) < X := by
    have := lt_of_mul_lt_mul_right hpos hMpos.le; exact_mod_cast this
  have h2 : X ≤ ma * (ma + 1) := by
    have he : ((ma * (ma + 1) : ℤ) : ℝ) * M + M = (((ma * (ma + 1) + 1 : ℤ)) : ℝ) * M := by
      push_cast; ring
    rw [he] at hupp'x
    have : X < ma * (ma + 1) + 1 := by
      have := lt_of_mul_lt_mul_right hupp'x hMpos.le; exact_mod_cast this
    omega
  omega
private theorem rndSqrt_core {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    (hx : 0 < x)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (hxrep : ∃ mx : ℤ, x = (mx : ℝ) * (2 : ℝ) ^ (F₁.canonicalExp x))
    (hf1 : 2 * F₁.canonicalExp (Real.sqrt x) ≤ F₁.canonicalExp x)
    (hle : F₁.canonicalExp (Real.sqrt x) ≤ Int.log 2 (Real.sqrt x) + 1)
    (hquant : F₂.canonicalExp (Real.sqrt x) + Int.log 2 (Real.sqrt x) + 1
                ≤ 2 * F₁.canonicalExp (Real.sqrt x) - 2)
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) (Real.sqrt x) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) (Real.sqrt x) w :=
  round_round_mid_cases hundef₁ (Real.sqrt_pos.mpr hx) (by omega) hle hz hw
    (fun hmid => absurd hmid (not_le.mpr (round_round_sqrt_aux hx hxrep hf1 hle hquant)))
private theorem rndSqrt_of {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x : Dyadic} (hx : x ∈ F₁) (hxnn : 0 ≤ (x : ℝ))
    (hexps : 0 < (x : ℝ) →
      2 * F₁.canonicalExp (Real.sqrt x) ≤ F₁.canonicalExp x ∧
      F₁.canonicalExp (Real.sqrt x) ≤ Int.log 2 (Real.sqrt x) + 1 ∧
      F₂.canonicalExp (Real.sqrt x) + Int.log 2 (Real.sqrt x) + 1
        ≤ 2 * F₁.canonicalExp (Real.sqrt x) - 2)
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) (Real.sqrt (x : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) (Real.sqrt (x : ℝ)) w := by
  rcases eq_or_lt_of_le hxnn with hx0 | hxpos
  · rw [← hx0, Real.sqrt_zero, show (0 : ℝ) = ((0 : Dyadic) : ℝ) from by simp] at hz ⊢
    exact rndExact (FiniteFormat.zero_mem F₂.unbounded) hz hw
  obtain ⟨c, _, hc⟩ := exists_canonical_rep F₁ hp₁ hx hxpos
  obtain ⟨h1, h2, h3⟩ := hexps hxpos
  exact rndSqrt_core hxpos hundef₁ ⟨c, hc⟩ h1 h2 h3 hz hw
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ + 2 ≤ p₂)
    (hexp₁ : F₁.exp = ⊥) (hexp₂ : F₂.exp = ⊥)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x : Dyadic} (hx : x ∈ F₁) (hxpos : 0 ≤ (x : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) (Real.sqrt (x : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) (Real.sqrt (x : ℝ)) w := by
  refine rndSqrt_of hp₁ hundef₁ hx hxpos (fun hxpos => ?_) hz hw
  have hs_pos : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hxpos
  have habs : |Real.sqrt (x : ℝ)| = Real.sqrt (x : ℝ) := abs_of_pos hs_pos
  have hp₁ℤ : (1 : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast F₁.p_pos hp₁
  have hpp' : 2 * (p₁ : ℤ) + 2 ≤ (p₂ : ℤ) := by omega
  obtain ⟨hloglo, hloghi⟩ := log_sqrt_bounds hxpos
  have hcE1s : F₁.canonicalExp (Real.sqrt (x : ℝ))
      = Int.log 2 (Real.sqrt (x : ℝ)) + 1 - (p₁ : ℤ) := by
    rw [canonicalExp_expBot hp₁ hexp₁ (ne_of_gt hs_pos), habs]
  have hcE2s : F₂.canonicalExp (Real.sqrt (x : ℝ))
      = Int.log 2 (Real.sqrt (x : ℝ)) + 1 - (p₂ : ℤ) := by
    rw [canonicalExp_expBot hp₂ hexp₂ (ne_of_gt hs_pos), habs]
  have hcE1x : F₁.canonicalExp (x : ℝ) = Int.log 2 (x : ℝ) + 1 - (p₁ : ℤ) := by
    rw [canonicalExp_expBot hp₁ hexp₁ (ne_of_gt hxpos), abs_of_pos hxpos]
  exact ⟨by rw [hcE1s, hcE1x]; omega, by rw [hcE1s]; omega, by rw [hcE1s, hcE2s]; omega⟩
end Mpfx
