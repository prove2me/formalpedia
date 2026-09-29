-- Prove2me | solution 1 for mme_entropy_penalty_le_pair_reference
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:55:54.412976+00:00
-- url     : https://prove2.me/submissions/4b96d394-f70c-4e45-b7c0-1418b1c02913

import Theorems.Thm_mme_split_pair_product_mass_le
import Theorems.Thm_mme_entropy_penalty_le_product_dual

open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit

/-- Any two positive coordinate probability distributions give an explicit
upper bound on the split entropy penalty. No split-mass certificate is needed. -/
theorem solution
    {half : ℕ} {parent : Fin 3 → ℕ} (alpha : Split half parent → ℝ)
    (ha : ∀ c, 0 ≤ alpha c) (hprob : ∑ c, alpha c = 1)
    (i j : Fin 3) (hij : i ≠ j) (p q : Fin (half + 1) → ℝ)
    (hp : ∀ a, 0 < p a) (hq : ∀ b, 0 < q b)
    (hpmass : ∑ a, p a = 1) (hqmass : ∑ b, q b = 1) :
    Real.log 2 * entropyPenalty alpha ≤
      -(∑ a, mme_modern_marginal (fun c : Split half parent => c.val i) alpha a *
        Real.log (p a)) -
      (∑ b, mme_modern_marginal (fun c : Split half parent => c.val j) alpha b *
        Real.log (q b)) - entropy alpha := by
  let weights := fun k a => if k = i then p a else if k = j then q a else 1
  have hpos : ∀ k a, 0 < weights k a := by
    intro k a
    dsimp [weights]
    split_ifs <;> first | exact hp a | exact hq a | norm_num
  have hprod (c : Split half parent) :
      (∏ k, weights k (c.val k)) = p (c.val i) * q (c.val j) := by
    fin_cases i <;> fin_cases j <;>
      norm_num at hij <;> simp +decide [weights, Fin.prod_univ_three, show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;> ring
  have hmass : (∑ c : Split half parent, ∏ k, weights k (c.val k)) ≤ 1 := by
    simp_rw [hprod]
    calc
      _ ≤ (∑ a, p a) * (∑ b, q b) :=
        mme_split_pair_product_mass_le i j hij p q (fun a => (hp a).le)
          (fun b => (hq b).le)
      _ = 1 := by rw [hpmass, hqmass, one_mul]
  have hsum (M : Fin 3 → Fin (half + 1) → ℝ) :
      (∑ k, ∑ v, M k v * Real.log (weights k v)) =
        (∑ v, M i v * Real.log (p v)) + ∑ v, M j v * Real.log (q v) := by
    fin_cases i <;> fin_cases j <;>
      norm_num at hij <;> simp +decide [weights, Fin.sum_univ_three, show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;> ring
  have h := mme_entropy_penalty_le_product_dual alpha ha hprob weights hpos hmass
  rw [hsum] at h
  simpa only [neg_add, sub_eq_add_neg, add_assoc] using h


#print axioms solution
