-- Prove2me | solution 1 for mme_entropy_penalty_le_smoothed_counts
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:04:38.770221+00:00
-- url     : https://prove2.me/submissions/7fbc2f3a-6712-4e5f-b704-382ac0ebf379

import Theorems.Thm_mme_entropy_penalty_le_pair_reference

open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit

/-- Adding one to every coordinate count gives strictly positive reference
probabilities, even when some counts vanish. These references certify an
entropy-penalty bound using only their integer total-count identities. -/
theorem solution
    {half : ℕ} {parent : Fin 3 → ℕ} (alpha : Split half parent → ℝ)
    (ha : ∀ c, 0 ≤ alpha c) (hprob : ∑ c, alpha c = 1)
    (i j : Fin 3) (hij : i ≠ j) (D : ℕ)
    (a b : Fin (half + 1) → ℕ) (haD : ∑ v, a v = D) (hbD : ∑ v, b v = D) :
    Real.log 2 * entropyPenalty alpha ≤
      -(∑ v, mme_modern_marginal (fun c : Split half parent => c.val i) alpha v *
        Real.log (((a v : ℝ) + 1) / ((D : ℝ) + (half + 1)))) -
      (∑ v, mme_modern_marginal (fun c : Split half parent => c.val j) alpha v *
        Real.log (((b v : ℝ) + 1) / ((D : ℝ) + (half + 1)))) - entropy alpha := by
  have hden : 0 < (D : ℝ) + (half + 1) := by positivity
  have normalized (counts : Fin (half + 1) → ℕ) (hcounts : ∑ v, counts v = D) :
      ∑ v, ((counts v : ℝ) + 1) / ((D : ℝ) + (half + 1)) = 1 := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    simp only [Finset.sum_add_distrib, ← Nat.cast_sum, hcounts, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_add,
      Nat.cast_one]
    exact mul_inv_cancel₀ hden.ne'
  exact mme_entropy_penalty_le_pair_reference alpha ha hprob i j hij
    (fun v => ((a v : ℝ) + 1) / ((D : ℝ) + (half + 1)))
    (fun v => ((b v : ℝ) + 1) / ((D : ℝ) + (half + 1)))
    (fun v => div_pos (by positivity) hden)
    (fun v => div_pos (by positivity) hden) (normalized a haD) (normalized b hbD)


#print axioms solution
