-- Prove2me | solution 1 for mme_rational_product_dual_penalty_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T11:34:51.384479+00:00
-- url     : https://prove2.me/submissions/810b2ea0-3f28-4785-ae13-b56cee93c568

import Theorems.Thm_mme_entropy_penalty_le_product_dual

open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit

/-- Certified logarithm enclosures and a normalized rational product dual give
a rational upper bound for the maximum-entropy penalty, including zero atoms. -/
theorem solution
    {half : ℕ} {parent : Fin 3 → ℕ}
    (alpha : Split half parent → ℚ)
    (ha : ∀ c, 0 ≤ alpha c) (hprob : ∑ c, alpha c = 1)
    (weights : Fin 3 → Fin (half + 1) → ℚ)
    (hpos : ∀ i j, 0 < weights i j)
    (hmass : ∑ c : Split half parent, ∏ i, weights i (c.val i) ≤ 1)
    (weightLower : Fin 3 → Fin (half + 1) → ℚ)
    (alphaUpper : Split half parent → ℚ)
    (hwlog : ∀ i j, (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ))
    (halog : ∀ c, 0 < alpha c → Real.log (alpha c : ℝ) ≤ (alphaUpper c : ℝ))
    (bound : ℚ) :
    let m := fun i j => ∑ c : {c : Split half parent // c.val i = j}, alpha c.val;
    -(∑ i, ∑ j, m i j * weightLower i j) + ∑ c, alpha c * alphaUpper c ≤ bound →
      Real.log 2 * entropyPenalty (fun c => (alpha c : ℝ)) ≤ (bound : ℝ) := by
  intro m hcert
  have haR (c : Split half parent) : (0 : ℝ) ≤ alpha c := by exact_mod_cast ha c
  have hmcast (i : Fin 3) (j : Fin (half + 1)) :
      (m i j : ℝ) = mme_modern_marginal (fun c : Split half parent => c.val i)
        (fun c => (alpha c : ℝ)) j := by
    simp [m, mme_modern_marginal]
  have hmR (i : Fin 3) (j : Fin (half + 1)) : (0 : ℝ) ≤ m i j := by
    have h : 0 ≤ m i j := Finset.sum_nonneg (fun c _ => ha c.val)
    exact_mod_cast h
  have hpen := mme_entropy_penalty_le_product_dual (fun c => (alpha c : ℝ))
    haR (by dsimp only; exact_mod_cast hprob) (fun i j => (weights i j : ℝ))
    (fun i j => by dsimp only; exact_mod_cast hpos i j)
    (by dsimp only; exact_mod_cast hmass)
  simp_rw [← hmcast] at hpen
  have hcross :
      -(∑ i, ∑ j, (m i j : ℝ) * Real.log (weights i j : ℝ)) ≤
        -(∑ i, ∑ j, (m i j : ℝ) * (weightLower i j : ℝ)) := by
    apply neg_le_neg
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hwlog i j) (hmR i j)
  have halpha : -entropy (fun c => (alpha c : ℝ)) ≤
      ∑ c, (alpha c : ℝ) * (alphaUpper c : ℝ) := by
    simp only [entropy, Real.negMulLog_def, ← Finset.sum_neg_distrib, neg_mul, neg_neg]
    apply Finset.sum_le_sum
    intro c _
    by_cases hz : alpha c = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left
        (halog c (lt_of_le_of_ne (ha c) (Ne.symm hz))) (haR c)
  have hcertR := (Rat.cast_le (K := ℝ)).2 hcert
  push_cast at hcertR
  linarith


#print axioms solution
