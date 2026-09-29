-- Prove2me | solution 1 for Catalog.MachineLearning.NoiseFloor.ridge_optimal_iff_self_similar
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T00:20:57.73996+00:00
-- url     : https://prove2.me/submissions/6268a982-437d-455a-837d-08a9b13b7983

import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Definitions.Def_MachineLearning_NoiseFloor_NoiseFloorPrinciple
open Finset Catalog.MachineLearning.NoiseFloor in
theorem solution {ι : Type*} [Fintype ι] {a mu : ι → ℝ} {b lam : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : 0 < b)
    (hmu : ∀ i, 0 < mu i) (hlam : 0 < lam) :
    filterRisk a b (ridgeFilter mu lam) = noiseFloor a b ↔ ∀ i, a i * lam = mu i * b := by
  have hab : ∀ i, 0 < a i + b := fun i => by linarith [ha i]
  have hml : ∀ i, 0 < mu i + lam := fun i => by linarith [hmu i]
  -- per mode: `a(1-t)² + b t² - ab/(a+b) = (a+b)(t - a/(a+b))²`
  have hd : ∀ i, a i * (1 - ridgeFilter mu lam i) ^ 2 + b * (ridgeFilter mu lam i) ^ 2
      - b * (a i / (a i + b)) = (a i + b) * (ridgeFilter mu lam i - a i / (a i + b)) ^ 2 := by
    intro i
    have := (hab i).ne'
    field_simp
    ring
  have hdiff : filterRisk a b (ridgeFilter mu lam) - noiseFloor a b
      = ∑ i, (a i + b) * (ridgeFilter mu lam i - a i / (a i + b)) ^ 2 := by
    unfold filterRisk noiseFloor effDim
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl (fun i _ => hd i)
  have hnn : ∀ i ∈ (univ : Finset ι), 0 ≤ (a i + b) * (ridgeFilter mu lam i - a i / (a i + b)) ^ 2 :=
    fun i _ => mul_nonneg (hab i).le (sq_nonneg _)
  rw [← sub_eq_zero, hdiff, sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · -- every mode must use the Wiener shrinkage
    intro h i
    rcases mul_eq_zero.1 (h i (mem_univ i)) with h1 | h1
    · exact absurd h1 (hab i).ne'
    · have h2 := sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1)
      unfold ridgeFilter at h2
      rw [div_eq_div_iff (hml i).ne' (hab i).ne'] at h2
      linarith
  · intro h i _
    have h2 : ridgeFilter mu lam i - a i / (a i + b) = 0 := by
      unfold ridgeFilter
      rw [div_sub_div _ _ (hml i).ne' (hab i).ne']
      have : mu i * (a i + b) - (mu i + lam) * a i = 0 := by linarith [h i]
      rw [this, zero_div]
    rw [h2]
    ring
