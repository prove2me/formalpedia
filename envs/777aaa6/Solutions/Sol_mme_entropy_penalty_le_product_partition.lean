-- Prove2me | solution 1 for mme_entropy_penalty_le_product_partition
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:54:12.892972+00:00
-- url     : https://prove2.me/submissions/8aef6f59-4e49-45b3-aaa1-b6fcf5e909fd

import Theorems.Thm_mme_entropy_penalty_le_product_dual

open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit

/-- Arbitrary positive product weights bound the entropy penalty after accounting
for their partition function. No approximate normalization assumption is needed. -/
theorem solution
    {half : ℕ} {parent : Fin 3 → ℕ} (alpha : Split half parent → ℝ)
    (ha : ∀ c, 0 ≤ alpha c) (hprob : ∑ c, alpha c = 1)
    (weights : Fin 3 → Fin (half + 1) → ℝ)
    (hpos : ∀ i j, 0 < weights i j)
    (Z : ℝ) (hZ : 0 < Z)
    (hpartition : ∑ c : Split half parent, ∏ i, weights i (c.val i) = Z) :
    Real.log 2 * entropyPenalty alpha ≤
      Real.log Z -
        (∑ i, ∑ j, mme_modern_marginal (fun c : Split half parent => c.val i) alpha j *
          Real.log (weights i j)) - entropy alpha := by
  classical
  let normalized := fun (i : Fin 3) j => if i = 0 then weights i j / Z else weights i j
  have hnpos : ∀ i j, 0 < normalized i j := by
    intro i j
    dsimp [normalized]
    split_ifs
    · exact div_pos (hpos i j) hZ
    · exact hpos i j
  have hprod (c : Split half parent) :
      (∏ i, normalized i (c.val i)) = (∏ i, weights i (c.val i)) / Z := by
    simp [Fin.prod_univ_succ, normalized]
    ring
  have hmass : ∑ c : Split half parent, ∏ i, normalized i (c.val i) ≤ 1 := by
    simp_rw [hprod]
    simp only [div_eq_mul_inv, ← Finset.sum_mul, hpartition, mul_inv_cancel₀ hZ.ne',
      le_refl]
  have hmarg :
      ∑ j, mme_modern_marginal (fun c : Split half parent => c.val 0) alpha j = 1 := by
    exact (Fintype.sum_fiberwise (fun c : Split half parent => c.val 0) alpha).trans hprob
  have hlog (i : Fin 3) (j : Fin (half + 1)) :
      Real.log (normalized i j) =
        Real.log (weights i j) - if i = 0 then Real.log Z else 0 := by
    by_cases hi : i = 0
    · simp [normalized, hi, Real.log_div (hpos 0 j).ne' hZ.ne']
    · simp [normalized, hi]
  have hcorrection :
      (∑ i : Fin 3, ∑ j, mme_modern_marginal
        (fun c : Split half parent => c.val i) alpha j *
          (if i = 0 then Real.log Z else 0)) = Real.log Z := by
    simp_rw [mul_ite, mul_zero]
    simp [← Finset.sum_mul, hmarg]
  have h := mme_entropy_penalty_le_product_dual alpha ha hprob
    normalized hnpos hmass
  simp_rw [hlog, mul_sub, Finset.sum_sub_distrib] at h
  rw [hcorrection] at h
  linarith


#print axioms solution
