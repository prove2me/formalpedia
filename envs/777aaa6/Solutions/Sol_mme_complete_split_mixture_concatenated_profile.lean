-- Prove2me | solution 1 for mme_complete_split_mixture_concatenated_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T21:23:20.553724+00:00
-- url     : https://prove2.me/submissions/ccce8a10-0304-432a-a94a-fff0f3dd46b3

import Definitions.Def_mme_complete_split_concatenation

open BigOperators MME.CompleteSplit

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution {R : Type u} [Fintype R]
    (ell : ℕ) (hell : 1 ≤ ell)
    (weights : R → ℝ) (hw : ∀ r, 0 ≤ weights r)
    (hsumw : ∑ r, weights r = 1) (p q : R → Profile ell) :
    ∃ beta : Profile (ell + 1),
      (∀ w, beta.probability w =
        mixedProbability weights
          (fun r ↦ concatenatedProbability hell (p r).probability (q r).probability) w) ∧
      (∀ x y, beta.probability ((completeWordSplitEquiv ell hell).symm (x, y)) =
        ∑ r, weights r * ((p r).probability x * (q r).probability y)) ∧
      (∀ x, ∑ y, beta.probability ((completeWordSplitEquiv ell hell).symm (x, y)) =
        ∑ r, weights r * (p r).probability x) ∧
      (∀ y, ∑ x, beta.probability ((completeWordSplitEquiv ell hell).symm (x, y)) =
        ∑ r, weights r * (q r).probability y) := by
  let f := mixedProbability weights
    (fun r ↦ concatenatedProbability hell (p r).probability (q r).probability)
  have hf : ∀ w, 0 ≤ f w := by
    intro w
    apply Finset.sum_nonneg
    intro r _
    exact mul_nonneg (hw r) (mul_nonneg ((p r).nonnegative _) ((q r).nonnegative _))
  have hsumchild (r : R) :
      ∑ w, concatenatedProbability hell (p r).probability (q r).probability w = 1 := by
    calc
      _ = ∑ xy : CompleteWord ell × CompleteWord ell,
          (p r).probability xy.1 * (q r).probability xy.2 :=
        (completeWordSplitEquiv ell hell).sum_comp
          (fun xy ↦ (p r).probability xy.1 * (q r).probability xy.2)
      _ = 1 := by
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum, (q r).sum_eq_one, mul_one]
        exact (p r).sum_eq_one
  have hsum : ∑ w, f w = 1 := by
    change (∑ w, ∑ r, weights r *
      concatenatedProbability hell (p r).probability (q r).probability w) = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hsumchild, mul_one]
    exact hsumw
  let beta : Profile (ell + 1) := ⟨by omega, f, hf, hsum⟩
  have happ (x y : CompleteWord ell) :
      beta.probability ((completeWordSplitEquiv ell hell).symm (x, y)) =
        ∑ r, weights r * ((p r).probability x * (q r).probability y) := by
    change mixedProbability weights _ _ = _
    simp only [mixedProbability, concatenatedProbability, Equiv.apply_symm_apply]
  refine ⟨beta, fun _ ↦ rfl, happ, ?_, ?_⟩
  · intro x
    simp_rw [happ]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [← Finset.mul_sum, ← Finset.mul_sum, (q r).sum_eq_one, mul_one]
  · intro y
    simp_rw [happ]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [← Finset.mul_sum, ← Finset.sum_mul, (p r).sum_eq_one, one_mul]
