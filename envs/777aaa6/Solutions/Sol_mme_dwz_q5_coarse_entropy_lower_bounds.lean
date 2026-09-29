-- Prove2me | solution 1 for mme_dwz_q5_coarse_entropy_lower_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-18T14:04:58.608727+00:00
-- url     : https://prove2.me/submissions/e53027d8-8024-4fd4-880a-6186d3312e00

import Definitions.Def_mme_dwz_q5_global_asymptotic_data
import Theorems.Thm_mme_dwz_q5_exact_global_profile_certificate
import Theorems.Thm_mme_log_interval_of_exact_rational_series_certificate
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

open BigOperators MME.DWZQ5ExactData MME.DWZQ5AsymptoticData
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace MME.DWZB2Positivity

private theorem denominator_product_pos : 0 < D :=
  Finset.prod_pos (fun c _ ↦ (rawProfile c).denominator_pos)

private theorem occurrence_eq (t : ℕ) (c : Fin 45) :
    n t c = component c * (D * t) := by
  apply Nat.mul_div_cancel'
  have hc : (rawProfile c).denominator ∣ D :=
    Finset.dvd_prod_of_mem (fun d : Fin 45 ↦ (rawProfile d).denominator)
      (Finset.mem_univ c)
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hc t) (component c)

private theorem total_eq (t : ℕ) : N t = scale * (D * t) := by
  simp only [N, occurrence_eq, ← Finset.sum_mul,
    mme_dwz_q5_exact_global_profile_certificate.2.2.1]

private theorem total_one_pos : 0 < N 1 := by
  rw [total_eq, mul_one]
  exact Nat.mul_pos mme_dwz_q5_exact_global_profile_certificate.1 denominator_product_pos

theorem entropy_ge_log_inverse_max {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (b : ℝ) (hb : 0 < b) (hmax : ∀ i, p i ≤ b) :
    Real.log b⁻¹ ≤ ∑ i, Real.negMulLog (p i) := by
  have hterm (i : ι) : p i * Real.log b⁻¹ ≤ Real.negMulLog (p i) := by
    by_cases hi : p i = 0
    · simp [hi]
    · have hlog := (Real.log_le_log_iff
        (lt_of_le_of_ne (hp i) (Ne.symm hi)) hb).mpr (hmax i)
      rw [Real.log_inv, Real.negMulLog]
      nlinarith [mul_le_mul_of_nonneg_left hlog (hp i)]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hterm i)
  simpa only [← Finset.sum_mul, hsum, one_mul] using h

theorem normalized_mass_entropy {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (s : ℝ) (hs : 0 < s)
    (hsum : ∑ i, a i = s) :
    (s * Real.log s - ∑ i, a i * Real.log (a i)) / s =
      ∑ i, Real.negMulLog (a i / s) := by
  have hterm (i : ι) : Real.negMulLog (a i / s) =
      (a i * Real.log s - a i * Real.log (a i)) / s := by
    rw [Real.negMulLog, Real.log_div (ne_of_gt (ha i)) (ne_of_gt hs)]
    ring
  simp only [hterm, ← Finset.sum_div, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hsum]

theorem component_max : ∀ c : Fin 45, 100 * component c ≤ 13 * scale := by
  decide +kernel

theorem marginal_max : ∀ (i : Fin 3) (g : Fin 9),
    25 * marginal i g ≤ 9 * scale := by
  decide +kernel

theorem targetRate_entropy : targetRate =
    ∑ c : Fin 45, Real.negMulLog ((component c : ℝ) / scale) := by
  have hs : (0 : ℝ) < scale := by
    exact_mod_cast mme_dwz_q5_exact_global_profile_certificate.1
  have hd : (0 : ℝ) < D := by exact_mod_cast denominator_product_pos
  have hn (c : Fin 45) : (0 : ℝ) < n 1 c := by
    rw [occurrence_eq, mul_one, Nat.cast_mul]
    exact mul_pos (by exact_mod_cast
      mme_dwz_q5_exact_global_profile_certificate.2.1 c) hd
  rw [targetRate, normalized_mass_entropy (fun c : Fin 45 ↦ (n 1 c : ℝ)) hn
    (N 1 : ℝ) (by exact_mod_cast total_one_pos)
    (by simp only [N, Nat.cast_sum])]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  rw [occurrence_eq, total_eq, mul_one,
    Nat.cast_mul, Nat.cast_mul]
  field_simp

theorem targetRate_min_entropy : Real.log (100 / 13 : ℝ) ≤ targetRate := by
  have hs : (0 : ℝ) < scale := by
    exact_mod_cast mme_dwz_q5_exact_global_profile_certificate.1
  rw [targetRate_entropy]
  have h := entropy_ge_log_inverse_max
    (fun c : Fin 45 ↦ (component c : ℝ) / scale)
    (fun c ↦ div_nonneg (Nat.cast_nonneg _) hs.le)
    (by rw [← Finset.sum_div, ← Nat.cast_sum,
      mme_dwz_q5_exact_global_profile_certificate.2.2.1]; exact div_self hs.ne')
    (13 / 100) (by norm_num) (fun c ↦ ?_)
  · norm_num at h ⊢
    exact h
  · apply (div_le_iff₀ hs).mpr
    have hc : (100 : ℝ) * component c ≤ 13 * scale := by
      exact_mod_cast component_max c
    linarith

theorem marginal_min_entropy (i : Fin 3) :
    Real.log (25 / 9 : ℝ) ≤ marginalEntropy i := by
  have hs : (0 : ℝ) < scale := by
    exact_mod_cast mme_dwz_q5_exact_global_profile_certificate.1
  have hsum : (∑ g : Fin 9, marginal i g) = scale :=
    mme_dwz_q5_exact_global_profile_certificate.2.2.2.2.2.2.2.1 i
  have h := entropy_ge_log_inverse_max
    (fun g : Fin 9 ↦ (marginal i g : ℝ) / scale)
    (fun g ↦ div_nonneg (Nat.cast_nonneg _) hs.le)
    (by rw [← Finset.sum_div, ← Nat.cast_sum, hsum]; exact div_self hs.ne')
    (9 / 25) (by norm_num) (fun g ↦ ?_)
  · norm_num at h
    exact h
  · apply (div_le_iff₀ hs).mpr
    have hc : (25 : ℝ) * marginal i g ≤ 9 * scale := by
      exact_mod_cast marginal_max i g
    linarith

theorem log_target_lower : (46 / 25 : ℝ) ≤ Real.log (100 / 13 : ℝ) := by
  have h := (mme_log_interval_of_exact_rational_series_certificate
    (100 / 13) (87 / 113) (46 / 25) 10 0 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])).1
  norm_num at h
  exact h

theorem log_marginal_lower : (101 / 100 : ℝ) ≤ Real.log (25 / 9 : ℝ) := by
  have h := (mme_log_interval_of_exact_rational_series_certificate
    (25 / 9) (8 / 17) (101 / 100) 10 0 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])).1
  norm_num at h
  exact h

theorem targetRate_lower : (46 / 25 : ℝ) ≤ targetRate :=
  log_target_lower.trans targetRate_min_entropy

theorem marginalEntropy_lower (i : Fin 3) :
    (101 / 100 : ℝ) ≤ marginalEntropy i :=
  log_marginal_lower.trans (marginal_min_entropy i)

theorem extractionRate_positive_of_compatibility_bound
    (hW : compatibilityRate ≤ targetRate - marginalEntropy 2) :
    (1 / 100 : ℝ) < extractionRate := by
  have hU : (DWZFourthGlobalWitness.entropyUpper : ℝ) < 71 / 25 := by
    norm_num [DWZFourthGlobalWitness.entropyUpper]
  have hT := targetRate_lower
  have hX := marginalEntropy_lower 0
  have hY := marginalEntropy_lower 1
  have hZ := marginalEntropy_lower 2
  unfold extractionRate hashRate
  have h0 : 0 < targetRate - 1 / 100 := by linarith
  have hx : (DWZFourthGlobalWitness.entropyUpper : ℝ) - marginalEntropy 0 <
      targetRate - 1 / 100 := by linarith
  have hy : (DWZFourthGlobalWitness.entropyUpper : ℝ) - marginalEntropy 1 <
      targetRate - 1 / 100 := by linarith
  have hw : compatibilityRate < targetRate - 1 / 100 := by linarith
  have hh := max_lt h0 (max_lt hx (max_lt hy hw))
  linarith

end MME.DWZB2Positivity

theorem solution :
    (46 / 25 : ℝ) ≤ MME.DWZQ5AsymptoticData.targetRate ∧
    ∀ mode : Fin 3, (101 / 100 : ℝ) ≤
      MME.DWZQ5AsymptoticData.marginalEntropy mode :=
  ⟨MME.DWZB2Positivity.targetRate_lower,
    MME.DWZB2Positivity.marginalEntropy_lower⟩

