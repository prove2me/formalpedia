-- Prove2me | solution 1 for mme_same_marginal_entropy_le_product_dual
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:41:12.225473+00:00
-- url     : https://prove2.me/submissions/9900e30f-280f-4a9c-8d18-3e5f6c780cdf

import Theorems.Thm_mme_entropy_le_cross_entropy
import Definitions.Def_mme_recursive_thin_split_data

open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit

private theorem marginal_weighted_sum {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] (f : A → B) (p : A → ℝ) (w : B → ℝ) :
    ∑ a, p a * w (f a) = ∑ b, mme_modern_marginal f p b * w b := by
  classical
  rw [← Fintype.sum_fiberwise f (fun a => p a * w (f a))]
  apply Finset.sum_congr rfl
  intro b _
  simp only [mme_modern_marginal, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [a.property]

/-- Positive coordinate weights whose product has total mass at most one
bound the entropy of every distribution with the prescribed marginals. -/
theorem solution
    {half : ℕ} {parent : Fin 3 → ℕ} (alpha : Split half parent → ℝ)
    (weights : Fin 3 → Fin (half + 1) → ℝ)
    (hpos : ∀ i j, 0 < weights i j)
    (hmass : ∑ c : Split half parent, ∏ i, weights i (c.val i) ≤ 1)
    (rho : Split half parent → ℝ) (hrho : rho ∈ SameMarginalDistributions alpha) :
    entropy rho ≤ -∑ i, ∑ j,
      mme_modern_marginal (fun c : Split half parent => c.val i) alpha j *
        Real.log (weights i j) := by
  have hq (c : Split half parent) : 0 < ∏ i, weights i (c.val i) :=
    Finset.prod_pos (fun i _ => hpos i (c.val i))
  have h := mme_entropy_le_cross_entropy rho (fun c => ∏ i, weights i (c.val i))
    hrho.1 (fun c => (hq c).le) hrho.2.1 hmass (fun c _ => hq c)
  have heq : (∑ c : Split half parent, rho c * Real.log (∏ i, weights i (c.val i))) =
      ∑ i, ∑ j, mme_modern_marginal (fun c : Split half parent => c.val i) alpha j *
        Real.log (weights i j) := by
    simp_rw [Real.log_prod (fun i _ => (hpos i _).ne'), Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [marginal_weighted_sum (fun c : Split half parent => c.val i) rho
      (fun j => Real.log (weights i j))]
    simp only [hrho.2.2]
  rw [heq] at h
  exact h


#print axioms solution
