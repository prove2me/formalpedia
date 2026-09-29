-- Prove2me | solution 1 for mme_regional_same_marginal_integer_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T20:52:11.940713+00:00
-- url     : https://prove2.me/submissions/f1443b6b-ef6d-4c6c-a75f-46987df2e160

import Theorems.Thm_mme_regional_mass_entropy_algebra
import Theorems.Thm_mme_regional_entropy_penalty_bound
import Mathlib
open BigOperators MME.RegionRate MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem solution {half : ℕ} {parent : Fin 3 → ℕ} (m v : Split half parent → ℕ) (n : ℕ)
    (hm : ∑ c, m c = n) (hv : ∑ c, v c = n)
    (hmargin : ∀ i j, (∑ c : {c : Split half parent // c.val i = j}, v c.val) =
      ∑ c : {c : Split half parent // c.val i = j}, m c.val) :
    0 ≤ (n : ℝ) * Real.log 2 * entropyPenalty (fun c ↦ (m c : ℝ) / n) ∧
    massEntropy (fun c ↦ (v c : ℝ)) ≤ massEntropy (fun c ↦ (m c : ℝ)) +
      (n : ℝ) * Real.log 2 * entropyPenalty (fun c ↦ (m c : ℝ) / n) := by
  classical
  by_cases hn : n = 0
  · have hm0 : ∀ c, m c = 0 := fun c ↦ Finset.sum_eq_zero_iff.mp (hm.trans hn) c (Finset.mem_univ c)
    have hv0 : ∀ c, v c = 0 := fun c ↦ Finset.sum_eq_zero_iff.mp (hv.trans hn) c (Finset.mem_univ c)
    simp [hn,hm0,hv0,massEntropy,entropy]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hsum (k : Split half parent → ℕ) (hk : ∑ c, k c = n) :
      ∑ c, (k c : ℝ) / n = 1 := by
    rw [← Finset.sum_div,show ∑ c, (k c : ℝ) = n by exact_mod_cast hk]
    exact div_self hnR
  have hnorm (k : Split half parent → ℕ) (hk : ∑ c, k c = n) :
      massEntropy (fun c ↦ (k c : ℝ)) = (n : ℝ) * entropy (fun c ↦ (k c : ℝ) / n) := by
    have hs : ∑ c, (k c : ℝ) = n := by exact_mod_cast hk
    rw [(mme_regional_mass_entropy_algebra (C := Unit) (W := Split half parent)).2.1 _
      (by rw [hs]; exact hnR),hs]
  have hpos (k : Split half parent → ℕ) (c : Split half parent) : 0 ≤ (k c : ℝ) / n := by positivity
  have h := mme_regional_entropy_penalty_bound (fun c ↦ (m c : ℝ) / n) (hpos m) (hsum m hm)
  have hvfeas : (fun c ↦ (v c : ℝ) / n) ∈ SameMarginalDistributions (fun c ↦ (m c : ℝ) / n) := by
    refine ⟨hpos v,hsum v hv,fun i j ↦ ?_⟩
    unfold mme_modern_marginal
    rw [← Finset.sum_div,← Finset.sum_div]
    congr 1
    exact_mod_cast hmargin i j
  refine ⟨mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (by norm_num)).le) h.1,?_⟩
  rw [hnorm v hv,hnorm m hm]
  have hh := mul_le_mul_of_nonneg_left (h.2 _ hvfeas) (Nat.cast_nonneg n)
  nlinarith
