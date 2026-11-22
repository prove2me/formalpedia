-- Prove2me | solution 1 for Mpfx.rndDiv_expFinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:54:27.722102+00:00
-- url     : https://prove2.me/submissions/d7a35e65-91a6-4dc3-9f5c-27803dfd1880

import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Definitions.Def_Mpfx_DoubleRounding_Div
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
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_exp_le_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_isEven_zero
import Theorems.Thm_Mpfx_FiniteFormat_log_sub_p_le_canonicalExp
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
import Theorems.Thm_Mpfx_IsFaithfulRound_eq_of_mem
import Theorems.Thm_Mpfx_IsFaithfulRound_nonneg
import Theorems.Thm_Mpfx_RoundsFinite_eq_of_mem
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
import Theorems.Thm_Mpfx_RoundsFinite_unique
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
import Theorems.Thm_Mpfx_canonicalExp_expFinite
import Theorems.Thm_Mpfx_exists_canonical_rep
import Theorems.Thm_Mpfx_exp_le_canonicalExp_coe
import Theorems.Thm_Mpfx_nearest_eq_of_close
import Theorems.Thm_Mpfx_nearest_error_le_half_ulp
import Theorems.Thm_Mpfx_rndDown_eq
import Theorems.Thm_Mpfx_rndDown_zero
import Theorems.Thm_Mpfx_rndExact
import Theorems.Thm_Mpfx_rndNeg
import Theorems.Thm_Mpfx_rndUp_zero
import Theorems.Thm_Mpfx_rnd_special
import Theorems.Thm_Mpfx_round_round_mid_cases
import Theorems.Thm_Mpfx_two_zpow_dbl
import Theorems.Thm_Mpfx_two_zpow_half
import Theorems.Thm_Mpfx_ulp_eq_zpow_of
import Theorems.Thm_Mpfx_ulp_guard_of_midp_ne
import Theorems.Thm_Mpfx_ulp_neg
import Theorems.Thm_Mpfx_ulp_of_ne_zero
import Theorems.Thm_Mpfx_ulp_pos
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
private theorem log_div_bounds {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Int.log 2 x - Int.log 2 y - 1 ≤ Int.log 2 (x / y) ∧
      Int.log 2 (x / y) ≤ Int.log 2 x - Int.log 2 y := by
  set Lx := Int.log 2 x with hLx
  set Ly := Int.log 2 y with hLy
  have hxy : 0 < x / y := div_pos hx hy
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  have hxlo : (2 : ℝ) ^ Lx ≤ x := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) hx; rw [← hLx] at this; exact_mod_cast this
  have hxhi : x < (2 : ℝ) ^ (Lx + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) x
    rw [← hLx] at this; exact_mod_cast this
  have hylo : (2 : ℝ) ^ Ly ≤ y := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) hy; rw [← hLy] at this; exact_mod_cast this
  have hyhi : y < (2 : ℝ) ^ (Ly + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) y
    rw [← hLy] at this; exact_mod_cast this
  have hlo : (2 : ℝ) ^ (Lx - Ly - 1) ≤ x / y := by
    rw [le_div_iff₀ hy]
    calc (2 : ℝ) ^ (Lx - Ly - 1) * y
        ≤ (2 : ℝ) ^ (Lx - Ly - 1) * (2 : ℝ) ^ (Ly + 1) :=
          mul_le_mul_of_nonneg_left hyhi.le (by positivity)
      _ = (2 : ℝ) ^ Lx := by rw [← zpow_add₀ hne]; congr 1; ring
      _ ≤ x := hxlo
  have hhi : x / y < (2 : ℝ) ^ (Lx - Ly + 1) := by
    rw [div_lt_iff₀ hy]
    calc x < (2 : ℝ) ^ (Lx + 1) := hxhi
      _ = (2 : ℝ) ^ (Lx - Ly + 1) * (2 : ℝ) ^ Ly := by rw [← zpow_add₀ hne]; congr 1; ring
      _ ≤ (2 : ℝ) ^ (Lx - Ly + 1) * y := mul_le_mul_of_nonneg_left hylo (by positivity)
  refine ⟨(Int.zpow_le_iff_le_log (b := 2) (by norm_num) hxy).mp (by exact_mod_cast hlo), ?_⟩
  have h2 : Int.log 2 (x / y) < Lx - Ly + 1 :=
    (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hxy).mp (by exact_mod_cast hhi)
  omega
private theorem midp_mem_F₂ {F₁ F₂ : FiniteFormat} {p₂ : ℕ}
    (hp₂ : F₂.p = (p₂ : Prec)) {v : ℝ} (hv : 0 < v)
    (hcexp : F₂.canonicalExp v ≤ F₁.canonicalExp v - 1)
    (hmid : v = midp F₁ v) :
    ∃ g : Dyadic, (g : ℝ) = v ∧ g ∈ F₂.unbounded := by
  set e₁ := F₁.canonicalExp v with he₁
  set e₂ := F₂.canonicalExp v with he₂
  set ma : ℤ := ⌊v * (2 : ℝ) ^ (-e₁)⌋ with hma
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  -- the midpoint dyadic and its realization
  have hg_real : (Dyadic.ofIntZpow (2 * ma + 1) (e₁ - 1) : ℝ) = v := by
    have hmidp : midp F₁ v = (ma : ℝ) * (2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₁ / 2 := by
      rw [midp, ulp_of_ne_zero F₁ hv.ne', rndDown_eq, ← he₁,
        ← hma, Dyadic.coe_ofIntZpow]
    rw [Dyadic.coe_ofIntZpow, hmid, hmidp, two_zpow_dbl e₁]; push_cast; ring
  -- `g` is a multiple of `2^(e₁−1)`, hence at any coarser quantum
  have hq_e₁ : Dyadic.quantumAtLeast ((e₁ - 1 : ℤ) : QExp)
      (Dyadic.ofIntZpow (2 * ma + 1) (e₁ - 1)) :=
    (Dyadic.quantumAtLeast_coe_real (e₁ - 1) _).mpr ⟨2 * ma + 1, by rw [Dyadic.coe_ofIntZpow]⟩
  have he₂le : (e₂ : QExp) ≤ ((e₁ - 1 : ℤ) : QExp) := by
    exact_mod_cast (show e₂ ≤ e₁ - 1 from by omega)
  -- `g = 𝒜(p₂, e₁−1, ⊤)`-representable, and that format is contained in
  -- `F₂.unbounded` by `𝒜-Contains-Prec` (`mem_unbounded_of_le`).
  have hF₂le : F₂.exp ≤ ((e₁ - 1 : ℤ) : QExp) :=
    le_trans (exp_le_canonicalExp_coe F₂ v) (by rw [← he₂]; exact he₂le)
  refine ⟨Dyadic.ofIntZpow (2 * ma + 1) (e₁ - 1), hg_real,
    Format.mem_unbounded_of_le (p := (p₂ : Prec))
      (e := ((e₁ - 1 : ℤ) : QExp)) (le_of_eq hp₂.symm) hF₂le ?_ hq_e₁⟩
  -- precisionAtMost p₂: mantissa at scale e₂ fits p₂ bits
  rw [Dyadic.precisionAtMost_coe_real]
  have hq_e₂ := Dyadic.quantumAtLeast_anti he₂le hq_e₁
  obtain ⟨C, hC⟩ := (Dyadic.quantumAtLeast_coe_real e₂ _).mp hq_e₂
  rw [hg_real] at hC
  refine ⟨C, e₂, by rw [hg_real]; exact hC, ?_⟩
  -- `|C| < 2^p₂` from `|v| < 2^(mag v) ≤ 2^(e₂ + p₂)`
  have h2e2 : (0 : ℝ) < (2 : ℝ) ^ e₂ := zpow_pos (by norm_num) _
  have hbound : Int.log 2 v + 1 ≤ e₂ + (p₂ : ℤ) := by
    have := FiniteFormat.log_sub_p_le_canonicalExp _ (ne_of_gt hv) hp₂
    rw [abs_of_pos hv, ← he₂] at this; omega
  have hvlt : |v| < (2 : ℝ) ^ (e₂ + (p₂ : ℤ)) := by
    rw [abs_of_pos hv]
    exact lt_of_lt_of_le (Int.lt_zpow_succ_log_self (b := 2) (by norm_num) v)
      (zpow_le_zpow_right₀ (by norm_num) hbound)
  have h2p2 : ((2 : ℝ) ^ p₂) = (2 : ℝ) ^ (p₂ : ℤ) := by rw [← zpow_natCast]
  have hsplit : (2 : ℝ) ^ (e₂ + (p₂ : ℤ)) = (2 : ℝ) ^ (p₂ : ℤ) * (2 : ℝ) ^ e₂ := by
    rw [show e₂ + (p₂ : ℤ) = (p₂ : ℤ) + e₂ from by ring, zpow_add₀ hne]
  have hCR : |(C : ℝ)| < (2 : ℝ) ^ (p₂ : ℤ) := by
    have hvC : |v| = |(C : ℝ)| * (2 : ℝ) ^ e₂ := by rw [hC, abs_mul, abs_of_pos h2e2]
    rw [hvC, hsplit] at hvlt
    exact lt_of_mul_lt_mul_right hvlt (le_of_lt h2e2)
  have hcast : (|C| : ℝ) < ((2 : ℤ) ^ p₂ : ℝ) := by push_cast; rw [h2p2]; exact hCR
  exact_mod_cast hcast
private theorem nearest_zero_of_small {F₁ : FiniteFormat} {tb₁ : TieBreak} {p₁ : ℕ} {emin₁ : ℤ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hexp₁ : F₁.exp = (emin₁ : QExp))
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x' : ℝ} (hx'0 : 0 ≤ x') (hx'lt : x' < (2 : ℝ) ^ (emin₁ - 1)) :
    RoundsFinite F₁.unbounded (.nearest tb₁) x' 0 := by
  have hz0 : ∀ e : ℤ, Dyadic.ofIntZpow 0 e = 0 := fun e =>
    (Dyadic.coe_real_inj _ _).mp (by simp)
  rcases eq_or_lt_of_le hx'0 with h0 | hpos
  · rw [← h0]
    have h := nearest_eq_of_close F₁ tb₁ 0 hundef₁ (m := 0)
      (by rw [zero_mul, Int.cast_zero, sub_zero, abs_zero]; norm_num)
    rwa [hz0] at h
  · have hcexp : F₁.canonicalExp x' = emin₁ := by
      rw [canonicalExp_expFinite hp₁ hexp₁ (ne_of_gt hpos), abs_of_pos hpos]
      have hlog : Int.log 2 x' < emin₁ - 1 :=
        (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hpos).mp (by exact_mod_cast hx'lt)
      omega
    have hclose : |x' * (2 : ℝ) ^ (-(F₁.canonicalExp x')) - ((0 : ℤ) : ℝ)| < 1 / 2 := by
      rw [hcexp, Int.cast_zero, sub_zero, abs_of_nonneg (by positivity)]
      rw [show (1 : ℝ) / 2 = (2 : ℝ) ^ (emin₁ - 1) * (2 : ℝ) ^ (-emin₁) from by
            rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                show (emin₁ - 1) + (-emin₁) = (-1 : ℤ) from by ring]; norm_num]
      exact mul_lt_mul_of_pos_right hx'lt (by positivity)
    have h := nearest_eq_of_close F₁ tb₁ x' hundef₁ hclose
    rwa [hz0] at h
private theorem round_round_div_zero {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak}
    {p₁ : ℕ} {emin₁ : ℤ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hexp₁ : F₁.exp = (emin₁ : QExp))
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {v : ℝ} (hv : 0 < v)
    (hvlt : v < (2 : ℝ) ^ (emin₁ - 1) - ulp F₂ v / 2)
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) v z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) v w := by
  have hu2pos : (0 : ℝ) < ulp F₂ v := ulp_pos F₂ hv.ne'
  have hv0 : RoundsFinite F₁.unbounded (.nearest tb₁) v 0 :=
    nearest_zero_of_small hp₁ hexp₁ hundef₁ hv.le (by linarith)
  have hznn : 0 ≤ (z : ℝ) := hz.isFaithfulRound.nonneg hv.le
  have hzerr := abs_le.mp (nearest_error_le_half_ulp hz)
  have hzlt : (z : ℝ) < (2 : ℝ) ^ (emin₁ - 1) := by linarith [hzerr.2, hvlt]
  have hz0 : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) 0 :=
    nearest_zero_of_small hp₁ hexp₁ hundef₁ hznn hzlt
  have hw0 : w = 0 := RoundsFinite.unique hundef₁ hw hz0
  rw [hw0]; exact hv0
private theorem round_round_div_aux {F₁ F₂ : FiniteFormat} {x y v : ℝ}
    (hy : 0 < y) (hv : x = v * y)
    (hxrep : ∃ mx : ℤ, x = (mx : ℝ) * (2 : ℝ) ^ (F₁.canonicalExp x))
    (hyrep : ∃ my : ℤ, y = (my : ℝ) * (2 : ℝ) ^ (F₁.canonicalExp y))
    (hA : F₂.canonicalExp v + Int.log 2 y ≤ F₁.canonicalExp x)
    (hB : F₂.canonicalExp v + Int.log 2 y ≤ F₁.canonicalExp v - 1 + F₁.canonicalExp y)
    (hne_mid : v ≠ midp F₁ v) :
    ulp F₂ v / 2 < |v - midp F₁ v| := by
  by_cases hg2 : v = 0 ∧ F₂.exp = ⊥
  · -- no `F₂` quantum at `0`: the left side vanishes and `hne_mid` gives the rest
    obtain ⟨rfl, hb⟩ := hg2
    rw [ulp, if_pos ⟨rfl, hb⟩]
    simpa using abs_pos.mpr (sub_ne_zero.mpr hne_mid)
  set e₁ := F₁.canonicalExp v with he₁
  set e₂ := F₂.canonicalExp v with he₂
  set ex := F₁.canonicalExp x
  set ey := F₁.canonicalExp y
  set Ly := Int.log 2 y with hLy
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  have hy_ne : y ≠ 0 := ne_of_gt hy
  set ma : ℤ := ⌊v * (2 : ℝ) ^ (-e₁)⌋ with hma
  have hmidp : midp F₁ v = ((2 * ma + 1 : ℤ) : ℝ) * (2 : ℝ) ^ (e₁ - 1) := by
    have hmv : midp F₁ v = (ma : ℝ) * (2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₁ / 2 := by
      rw [midp, ulp_eq_zpow_of F₁ (ulp_guard_of_midp_ne hne_mid), rndDown_eq, ← he₁,
        ← hma, Dyadic.coe_ofIntZpow]
    rw [hmv, two_zpow_dbl e₁]; push_cast; ring
  obtain ⟨mx, hmx⟩ := hxrep
  obtain ⟨my, hmy⟩ := hyrep
  -- integrality at the common scale `s = min(ex, e₁−1+ey)`
  set s : ℤ := min ex (e₁ - 1 + ey) with hs
  set dx : ℕ := (ex - s).toNat with hdx
  set dm : ℕ := (e₁ - 1 + ey - s).toNat with hdm
  have hdx_eq : (dx : ℤ) = ex - s := by rw [hdx, Int.toNat_of_nonneg (by omega)]
  have hdm_eq : (dm : ℤ) = e₁ - 1 + ey - s := by rw [hdm, Int.toNat_of_nonneg (by omega)]
  set K : ℤ := mx * 2 ^ dx - (2 * ma + 1) * my * 2 ^ dm with hK
  have e_ex : (2 : ℝ) ^ ex = (2 : ℝ) ^ dx * (2 : ℝ) ^ s := by
    rw [← zpow_natCast (2 : ℝ) dx, ← zpow_add₀ hne]; congr 1; omega
  have e_dm : (2 : ℝ) ^ (e₁ - 1) * (2 : ℝ) ^ ey = (2 : ℝ) ^ dm * (2 : ℝ) ^ s := by
    rw [← zpow_natCast (2 : ℝ) dm, ← zpow_add₀ hne, ← zpow_add₀ hne]; congr 1; omega
  have hdiff : x - midp F₁ v * y = (K : ℝ) * (2 : ℝ) ^ s := by
    rw [hmidp, hmx, hmy, hK]
    push_cast
    rw [e_ex, show (2 * (ma : ℝ) + 1) * (2 : ℝ) ^ (e₁ - 1) * ((my : ℝ) * (2 : ℝ) ^ ey)
          = (2 * (ma : ℝ) + 1) * (my : ℝ) * ((2 : ℝ) ^ (e₁ - 1) * (2 : ℝ) ^ ey) from by ring,
        e_dm]
    ring
  have hxmy_ne : x - midp F₁ v * y ≠ 0 := by
    rw [hv, ← sub_mul]; exact mul_ne_zero (sub_ne_zero.mpr hne_mid) hy_ne
  have hK_ne : K ≠ 0 := fun h0 => hxmy_ne (by rw [hdiff, h0]; simp)
  -- lower bound `|x − m·y| ≥ 2^s`
  have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hlow : (2 : ℝ) ^ s ≤ |x - midp F₁ v * y| := by
    rw [hdiff, abs_mul, abs_of_pos h2s_pos]
    have hKabs : (1 : ℝ) ≤ |(K : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |K| := Int.one_le_abs hK_ne
      calc (1 : ℝ) ≤ ((|K| : ℤ) : ℝ) := by exact_mod_cast h1
        _ = |(K : ℝ)| := by rw [Int.cast_abs]
    nlinarith [hKabs, h2s_pos]
  -- upper bound (from the negated conclusion)
  by_contra hcon
  rw [not_lt, show ulp F₂ v = (2 : ℝ) ^ e₂ from by rw [ulp_eq_zpow_of F₂ hg2, ← he₂]] at hcon
  have h2e2half : (2 : ℝ) ^ e₂ / 2 = (2 : ℝ) ^ (e₂ - 1) := two_zpow_half e₂
  have hupp : |x - midp F₁ v * y| < (2 : ℝ) ^ (e₂ + Ly) := by
    have hxmy_eq : |x - midp F₁ v * y| = |v - midp F₁ v| * y := by
      rw [hv, ← sub_mul, abs_mul, abs_of_pos hy]
    rw [hxmy_eq]
    have hylt : y < (2 : ℝ) ^ (Ly + 1) := by
      have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) y
      rw [← hLy] at this; exact_mod_cast this
    have hb : |v - midp F₁ v| * y ≤ (2 : ℝ) ^ (e₂ - 1) * y := by
      rw [← h2e2half]; exact mul_le_mul_of_nonneg_right hcon hy.le
    have hy2 : (2 : ℝ) ^ (e₂ - 1) * y < (2 : ℝ) ^ (e₂ - 1) * (2 : ℝ) ^ (Ly + 1) :=
      mul_lt_mul_of_pos_left hylt (by positivity)
    have heq : (2 : ℝ) ^ (e₂ - 1) * (2 : ℝ) ^ (Ly + 1) = (2 : ℝ) ^ (e₂ + Ly) := by
      rw [← zpow_add₀ hne]; congr 1; ring
    linarith [hb, hy2, heq]
  have hmono : (2 : ℝ) ^ (e₂ + Ly) ≤ (2 : ℝ) ^ s :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  linarith [hlow, hupp, hmono]
private theorem div_sep_bounds {F₁ F₂ : FiniteFormat} {p₁ : ℕ} (hp₁ : F₁.p = (p₁ : Prec))
    {a b : Dyadic} (hapos : 0 < (a : ℝ)) (hbpos : 0 < (b : ℝ))
    (hq₁ : F₂.canonicalExp ((a : ℝ) / b) ≤ Int.log 2 ((a : ℝ) / b) + 1 - p₁)
    (hq₂ : F₂.canonicalExp ((a : ℝ) / b) ≤ F₁.canonicalExp ((a : ℝ) / b) - p₁) :
    F₂.canonicalExp ((a : ℝ) / b) + Int.log 2 (b : ℝ) ≤ F₁.canonicalExp (a : ℝ) ∧
      F₂.canonicalExp ((a : ℝ) / b) + Int.log 2 (b : ℝ)
        ≤ F₁.canonicalExp ((a : ℝ) / b) - 1 + F₁.canonicalExp (b : ℝ) := by
  have hca := F₁.log_sub_p_le_canonicalExp (ne_of_gt hapos) hp₁
  have hcb := F₁.log_sub_p_le_canonicalExp (ne_of_gt hbpos) hp₁
  rw [abs_of_pos hapos] at hca
  rw [abs_of_pos hbpos] at hcb
  have := log_div_bounds hapos hbpos
  constructor <;> omega
private theorem rndDiv_core {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec))
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {a b : Dyadic} (ha : a ∈ F₁) (hb : b ∈ F₁)
    (hapos : 0 < (a : ℝ)) (hbpos : 0 < (b : ℝ))
    (hle : F₁.canonicalExp ((a : ℝ) / b) ≤ Int.log 2 ((a : ℝ) / b) + 1)
    (hquant : F₂.canonicalExp ((a : ℝ) / b) ≤ F₁.canonicalExp ((a : ℝ) / b) - (p₁ : ℤ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((a : ℝ) / b) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((a : ℝ) / b) w := by
  have hp1pos : (1 : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast F₁.p_pos hp₁
  obtain ⟨hA, hB⟩ := div_sep_bounds hp₁ hapos hbpos (by omega) hquant
  set v := (a : ℝ) / (b : ℝ) with hv_def
  have hv_pos : 0 < v := div_pos hapos hbpos
  have hab : (a : ℝ) = v * (b : ℝ) := by
    rw [hv_def]; exact (div_mul_cancel₀ (a : ℝ) (ne_of_gt hbpos)).symm
  have h21 : F₂.canonicalExp v < F₁.canonicalExp v := by omega
  refine round_round_mid_cases hundef₁ hv_pos h21 hle hz hw (fun hmid_le => ?_)
  by_cases heqmid : v = midp F₁ v
  · -- exact midpoint: `v ∈ F₂`, so the intermediate rounding is a no-op
    obtain ⟨g, hgv, hgmem⟩ := midp_mem_F₂ hp₂ hv_pos (by omega) heqmid
    have hzg : z = g := RoundsFinite.eq_of_mem hgmem (by rw [hgv]; exact hz)
    have hzv : (z : ℝ) = v := by rw [hzg, hgv]
    rw [← hzv]; exact hw
  · -- otherwise the separation lemma contradicts `hmid_le`
    obtain ⟨mx, _, hmx⟩ := exists_canonical_rep F₁ hp₁ ha hapos
    obtain ⟨my, _, hmy⟩ := exists_canonical_rep F₁ hp₁ hb hbpos
    exact absurd hmid_le (not_le.mpr
      (round_round_div_aux hbpos hab ⟨mx, hmx⟩ ⟨my, hmy⟩ hA hB heqmid))
private theorem rndDiv_pos_expFinite {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    {emin₁ emin₂ : ℤ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ ≤ p₂)
    (hexp₁ : F₁.exp = (emin₁ : QExp)) (hexp₂ : F₂.exp = (emin₂ : QExp))
    (hemin : emin₂ ≤ emin₁ - (p₁ : ℤ) - 2)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {a b : Dyadic} (ha : a ∈ F₁) (hb : b ∈ F₁)
    (hapos : 0 < (a : ℝ)) (hbpos : 0 < (b : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((a : ℝ) / (b : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((a : ℝ) / (b : ℝ)) w := by
  set v := (a : ℝ) / (b : ℝ) with hv_def
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hbpos
  have hv_pos : 0 < v := div_pos hapos hbpos
  have hp1pos : (1 : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast F₁.p_pos hp₁
  have hppZ : 2 * (p₁ : ℤ) ≤ (p₂ : ℤ) := by exact_mod_cast hpp
  by_cases hle : F₁.canonicalExp v ≤ Int.log 2 v + 1
  · -- normal: `F₂`'s step at `v` is `p₁` bits below `F₁`'s in either arm of the `max`
    refine rndDiv_core hp₁ hp₂ hundef₁ ha hb hapos hbpos hle ?_ hz hw
    rw [show (a : ℝ) / b = v from rfl]
    have h1 : emin₁ ≤ F₁.canonicalExp v := F₁.exp_le_canonicalExp v hexp₁
    have h2 := F₁.log_sub_p_le_canonicalExp (ne_of_gt hv_pos) hp₁
    rw [abs_of_pos hv_pos] at h2
    rw [canonicalExp_expFinite hp₂ hexp₂ (ne_of_gt hv_pos), abs_of_pos hv_pos]
    exact max_le (by omega) (by omega)
  · -- underflow regime: `cexp₁ v = emin₁ > mag v`
    rw [not_le] at hle
    have hhalf : ∀ k : ℤ, (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k / 2 := fun k => (two_zpow_half k).symm
    have hcvmax : F₁.canonicalExp v = max (Int.log 2 v + 1 - (p₁ : ℤ)) emin₁ := by
      rw [canonicalExp_expFinite hp₁ hexp₁ (ne_of_gt hv_pos), abs_of_pos hv_pos]
    have hcv_emin : F₁.canonicalExp v = emin₁ := by rw [hcvmax] at hle ⊢; omega
    have hcv2max : F₂.canonicalExp v = max (Int.log 2 v + 1 - (p₂ : ℤ)) emin₂ := by
      rw [canonicalExp_expFinite hp₂ hexp₂ (ne_of_gt hv_pos), abs_of_pos hv_pos]
    have hlogv_hi : Int.log 2 v + 1 ≤ emin₁ - 1 := by omega
    have hvhi : v < (2 : ℝ) ^ (Int.log 2 v + 1) :=
      Int.lt_zpow_succ_log_self (b := 2) (by norm_num) v
    have hvlt_thresh : v < (2 : ℝ) ^ (emin₁ - 1) :=
      lt_of_lt_of_le hvhi (zpow_le_zpow_right₀ (by norm_num) hlogv_hi)
    have hu2 : ulp F₂ v = (2 : ℝ) ^ (F₂.canonicalExp v) := ulp_of_ne_zero F₂ hv_pos.ne'
    by_cases hfar : v < (2 : ℝ) ^ (emin₁ - 1) - ulp F₂ v / 2
    · exact round_round_div_zero hp₁ hexp₁ hundef₁ hv_pos hfar hz hw
    · -- boundary sliver: impossible by the separation lemma
      exfalso
      rw [not_lt] at hfar
      -- `midp₁ v = 2^(emin₁−1)` (its `⌊·⌋` mantissa is `0`)
      have hma0 : ⌊v * (2 : ℝ) ^ (-(F₁.canonicalExp v))⌋ = 0 := by
        rw [hcv_emin, Int.floor_eq_zero_iff, Set.mem_Ico]
        refine ⟨by positivity, ?_⟩
        calc v * (2 : ℝ) ^ (-emin₁)
            < (2 : ℝ) ^ (emin₁ - 1) * (2 : ℝ) ^ (-emin₁) :=
              mul_lt_mul_of_pos_right hvlt_thresh (by positivity)
          _ = (2 : ℝ) ^ (-1 : ℤ) := by rw [← zpow_add₀ hne]; congr 1; ring
          _ < 1 := by norm_num
      have hmidp : midp F₁ v = (2 : ℝ) ^ (emin₁ - 1) := by
        rw [midp, ulp_of_ne_zero F₁ hv_pos.ne']
        rw [rndDown_eq, hcv_emin, Dyadic.coe_ofIntZpow,
            show ⌊v * (2 : ℝ) ^ (-emin₁)⌋ = 0 from by rw [← hcv_emin]; exact hma0]
        push_cast
        rw [hhalf emin₁]; ring
      have hne_mid : v ≠ midp F₁ v := by rw [hmidp]; exact ne_of_lt hvlt_thresh
      have hclose : |v - midp F₁ v| ≤ ulp F₂ v / 2 := by
        rw [hmidp, abs_of_nonpos (by linarith : v - (2 : ℝ) ^ (emin₁ - 1) ≤ 0)]; linarith
      -- bounds needed for `hA`/`hB` in the sliver: `Int.log v = emin₁ − 2`
      have hcv2_le : F₂.canonicalExp v ≤ emin₁ - (p₁ : ℤ) - 2 := by
        rw [hcv2max]; exact max_le (by omega) hemin
      have hLv_lo : emin₁ - 2 ≤ Int.log 2 v := by
        have hu2pos' := zpow_pos (show (0 : ℝ) < 2 by norm_num) (F₂.canonicalExp v)
        have h1 : ulp F₂ v / 2 ≤ (2 : ℝ) ^ (emin₁ - 2) := by
          rw [hu2]
          have hulp : (2 : ℝ) ^ (F₂.canonicalExp v) ≤ (2 : ℝ) ^ (emin₁ - 3) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
          have hle32 : (2 : ℝ) ^ (emin₁ - 3) ≤ (2 : ℝ) ^ (emin₁ - 2) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
          linarith [hulp, hle32, hu2pos']
        have hh : (2 : ℝ) ^ (emin₁ - 2) = (2 : ℝ) ^ (emin₁ - 1) / 2 := by
          rw [show (emin₁ - 2 : ℤ) = (emin₁ - 1) - 1 from by ring]; exact hhalf (emin₁ - 1)
        have hslv : (2 : ℝ) ^ (emin₁ - 2) ≤ v := by linarith [hfar, h1, hh]
        exact (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hv_pos).mp (by exact_mod_cast hslv)
      obtain ⟨mx, _, hmx⟩ := exists_canonical_rep F₁ hp₁ ha hapos
      obtain ⟨my, _, hmy⟩ := exists_canonical_rep F₁ hp₁ hb hbpos
      have hab : (a : ℝ) = v * (b : ℝ) := by
        rw [hv_def]; exact (div_mul_cancel₀ (a : ℝ) hbne).symm
      obtain ⟨hA, hB⟩ := div_sep_bounds (F₂ := F₂) hp₁ hapos hbpos
        (by rw [show (a : ℝ) / b = v from rfl]; omega)
        (by rw [show (a : ℝ) / b = v from rfl]; omega)
      have hsep := round_round_div_aux hbpos hab ⟨mx, hmx⟩ ⟨my, hmy⟩ hA hB hne_mid
      linarith [hsep, hclose]
private theorem rndDiv_posden_of_pos {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak}
    (hpos : DivPosCase F₁ F₂ tb₁ tb₂)
    {a b : Dyadic} (ha : a ∈ F₁) (hb : b ∈ F₁) (hbpos : 0 < (b : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((a : ℝ) / (b : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((a : ℝ) / (b : ℝ)) w := by
  rcases lt_trichotomy (a : ℝ) 0 with haneg | hazero | hapos
  · -- `a < 0`: negate the numerator (quotient flips sign), via `rndNeg`
    have hna : (-a) ∈ F₁ := FiniteFormat.neg_mem ha
    have hnapos : 0 < ((-a : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
    have hqval : ((-a : Dyadic) : ℝ) / (b : ℝ) = -((a : ℝ) / (b : ℝ)) := by
      rw [Dyadic.coe_real_neg, neg_div]
    refine rndNeg hz hw (fun hz' hw' => ?_)
    rw [← hqval] at hz' ⊢
    exact hpos (-a) b hna hb hnapos hbpos _ _ hz' hw'
  · -- `a = 0`: the quotient is `0`, exactly representable
    have hval : (a : ℝ) / (b : ℝ) = ((0 : Dyadic) : ℝ) := by rw [hazero, zero_div]; simp
    rw [hval] at hz ⊢
    exact rndExact (F₁ := F₁.unbounded) (F₂ := F₂.unbounded)
      (FiniteFormat.zero_mem F₂.unbounded) hz hw
  · exact hpos a b ha hb hapos hbpos z w hz hw
private theorem rndDiv_of_pos {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak}
    (hpos : DivPosCase F₁ F₂ tb₁ tb₂)
    {a b : Dyadic} (ha : a ∈ F₁) (hb : b ∈ F₁) (hbne : (b : ℝ) ≠ 0)
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((a : ℝ) / (b : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((a : ℝ) / (b : ℝ)) w := by
  rcases lt_or_gt_of_ne hbne with hbneg | hbpos
  · -- `b < 0`: `a/b = (−a)/(−b)`, positive denominator, value unchanged
    have hna : (-a) ∈ F₁ := FiniteFormat.neg_mem ha
    have hnb : (-b) ∈ F₁ := FiniteFormat.neg_mem hb
    have hnbpos : 0 < ((-b : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
    have hval : (a : ℝ) / (b : ℝ) = ((-a : Dyadic) : ℝ) / ((-b : Dyadic) : ℝ) := by
      rw [Dyadic.coe_real_neg, Dyadic.coe_real_neg, neg_div_neg_eq]
    rw [hval] at hz ⊢
    exact rndDiv_posden_of_pos hpos hna hnb hnbpos hz hw
  · exact rndDiv_posden_of_pos hpos ha hb hbpos hz hw
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    {emin₁ emin₂ : ℤ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ ≤ p₂)
    (hexp₁ : F₁.exp = (emin₁ : QExp)) (hexp₂ : F₂.exp = (emin₂ : QExp))
    (hemin : emin₂ ≤ emin₁ - (p₁ : ℤ) - 2)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {a b : Dyadic} (ha : a ∈ F₁) (hb : b ∈ F₁) (hbne : (b : ℝ) ≠ 0)
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((a : ℝ) / (b : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((a : ℝ) / (b : ℝ)) w :=
  rndDiv_of_pos (fun _ _ ha hb hapos hbpos _ _ hz hw =>
      rndDiv_pos_expFinite hp₁ hp₂ hpp hexp₁ hexp₂ hemin hundef₁ ha hb hapos hbpos hz hw)
    ha hb hbne hz hw
end Mpfx
