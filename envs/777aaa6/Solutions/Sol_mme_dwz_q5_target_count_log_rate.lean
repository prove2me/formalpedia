-- Prove2me | solution 1 for mme_dwz_q5_target_count_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-18T13:45:59.689697+00:00
-- url     : https://prove2.me/submissions/c63220be-ec23-4a57-afca-53b681b38629

import Definitions.Def_mme_dwz_q5_global_asymptotic_data
import Theorems.Thm_mme_scaled_multinomial_log_rate
import Theorems.Thm_mme_dwz_q5_exact_global_profile_certificate
import Mathlib.Tactic

open BigOperators Filter MME.DWZQ5ExactData MME.DWZQ5AsymptoticData
open scoped Topology Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace MME.DWZB2TargetRate

theorem D_pos : 0 < D := Finset.prod_pos (fun c _ ↦ (rawProfile c).denominator_pos)

theorem n_eq (t : ℕ) (c : Fin 45) : n t c = component c * (D * t) := by
  apply Nat.mul_div_cancel'
  have hc : (rawProfile c).denominator ∣ D :=
    Finset.dvd_prod_of_mem (fun d : Fin 45 ↦ (rawProfile d).denominator) (Finset.mem_univ c)
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hc t) (component c)

theorem n_scale (t : ℕ) (c : Fin 45) : n t c = n 1 c * t := by
  rw [n_eq, n_eq, mul_one, mul_assoc]

theorem N_scale (t : ℕ) : N t = N 1 * t := by
  simp only [N, n_scale t, Finset.sum_mul]

theorem N_eq (t : ℕ) : N t = scale * (D * t) := by
  simp only [N, n_eq, ← Finset.sum_mul,
    mme_dwz_q5_exact_global_profile_certificate.2.2.1]

theorem N_one_pos : 0 < N 1 := by
  rw [N_eq, mul_one]
  exact Nat.mul_pos mme_dwz_q5_exact_global_profile_certificate.1 D_pos

theorem N_tendsto : Tendsto N atTop atTop := by
  apply tendsto_atTop_mono (fun t ↦ ?_) tendsto_id
  rw [N_scale]
  exact Nat.le_mul_of_pos_left t N_one_pos

theorem targetCount_eq (t : ℕ) :
    targetCount t = Nat.multinomial Finset.univ (fun c ↦ n 1 c * t) := by
  simp only [targetCount, Nat.multinomial, N, n_scale t]

theorem target_log_rate :
    Tendsto (fun t : ℕ ↦ Real.log (targetCount t : ℝ) / (N t : ℝ))
      atTop (𝓝 targetRate) := by
  have h := (mme_scaled_multinomial_log_rate (n 1)).div_const (N 1 : ℝ)
  change Tendsto _ _ (𝓝 targetRate) at h
  convert h using 1
  funext t
  rw [targetCount_eq, N_scale, Nat.cast_mul]
  ring

theorem target_eventually_lower (a : ℝ) (ha : a < targetRate) :
    ∀ᶠ t : ℕ in atTop, Real.exp (a * (N t : ℝ)) ≤ (targetCount t : ℝ) := by
  have h := target_log_rate.eventually (lt_mem_nhds ha)
  filter_upwards [h, eventually_gt_atTop 0] with t ht ht0
  have hN : (0 : ℝ) < N t := by
    rw [N_scale, Nat.cast_mul]
    exact mul_pos (by exact_mod_cast N_one_pos) (by exact_mod_cast ht0)
  have hT : (0 : ℝ) < targetCount t := by
    rw [targetCount_eq]
    exact_mod_cast Nat.multinomial_pos (s := Finset.univ) (f := fun c ↦ n 1 c * t)
  have hl : a * (N t : ℝ) ≤ Real.log (targetCount t : ℝ) :=
    ((lt_div_iff₀ hN).mp ht).le
  exact (Real.le_log_iff_exp_le hT).mp hl

end MME.DWZB2TargetRate

set_option warningAsError true

theorem solution :
    (∀ (t : ℕ) (c : Fin 45), n t c = n 1 c * t) ∧
    0 < N 1 ∧
    (∀ t : ℕ, N t = N 1 * t) ∧
    Tendsto N atTop atTop ∧
    Tendsto (fun t : ℕ ↦ Real.log (targetCount t : ℝ) / (N t : ℝ))
      atTop (𝓝 targetRate) ∧
    ∀ a : ℝ, a < targetRate →
      ∀ᶠ t : ℕ in atTop, Real.exp (a * (N t : ℝ)) ≤ (targetCount t : ℝ) := by
  exact ⟨MME.DWZB2TargetRate.n_scale, MME.DWZB2TargetRate.N_one_pos,
    MME.DWZB2TargetRate.N_scale, MME.DWZB2TargetRate.N_tendsto,
    MME.DWZB2TargetRate.target_log_rate, MME.DWZB2TargetRate.target_eventually_lower⟩