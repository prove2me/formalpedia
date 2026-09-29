-- Prove2me | solution 1 for mme_complete_split_concatenated_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T21:22:13.337737+00:00
-- url     : https://prove2.me/submissions/85a690b9-6829-4249-b5d4-14afe944b09a

import Definitions.Def_mme_complete_split_concatenation

open BigOperators MME.CompleteSplit

set_option autoImplicit false
set_option warningAsError true

theorem solution (ell : ℕ) (hell : 1 ≤ ell) (p q : Profile ell) :
    ∃ beta : Profile (ell + 1),
      (∀ w, beta.probability w =
        concatenatedProbability hell p.probability q.probability w) ∧
      (∀ x y, beta.probability ((completeWordSplitEquiv ell hell).symm (x, y)) =
        p.probability x * q.probability y) ∧
      (∀ x, ∑ y, beta.probability ((completeWordSplitEquiv ell hell).symm (x, y)) =
        p.probability x) ∧
      (∀ y, ∑ x, beta.probability ((completeWordSplitEquiv ell hell).symm (x, y)) =
        q.probability y) := by
  let f := concatenatedProbability hell p.probability q.probability
  have hf : ∀ w, 0 ≤ f w := by
    intro w
    exact mul_nonneg (p.nonnegative _) (q.nonnegative _)
  have hsum : ∑ w, f w = 1 := by
    calc
      ∑ w, f w = ∑ xy : CompleteWord ell × CompleteWord ell,
          p.probability xy.1 * q.probability xy.2 :=
        (completeWordSplitEquiv ell hell).sum_comp
          (fun xy ↦ p.probability xy.1 * q.probability xy.2)
      _ = 1 := by
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum, q.sum_eq_one, mul_one]
        exact p.sum_eq_one
  let beta : Profile (ell + 1) :=
    ⟨by omega, f, hf, hsum⟩
  have happ (x y : CompleteWord ell) :
      beta.probability ((completeWordSplitEquiv ell hell).symm (x, y)) =
        p.probability x * q.probability y := by
    change concatenatedProbability hell p.probability q.probability _ = _
    simp only [concatenatedProbability, Equiv.apply_symm_apply]
  refine ⟨beta, fun _ ↦ rfl, happ, ?_, ?_⟩
  · intro x
    simp_rw [happ, ← Finset.mul_sum, q.sum_eq_one, mul_one]
  · intro y
    simp_rw [happ, ← Finset.sum_mul, p.sum_eq_one, one_mul]
