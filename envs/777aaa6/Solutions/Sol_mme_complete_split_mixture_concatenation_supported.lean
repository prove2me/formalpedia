-- Prove2me | solution 1 for mme_complete_split_mixture_concatenation_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T21:32:40.094363+00:00
-- url     : https://prove2.me/submissions/e512a402-4adb-4ed5-9557-652363ccb852

import Theorems.Thm_mme_complete_split_literal_concatenation_grade
import Theorems.Thm_mme_complete_split_mixture_concatenated_profile

open BigOperators MME.CompleteSplit

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution {R : Type u} [Fintype R]
    (ell : ℕ) (hell : 1 ≤ ell)
    (weights : R → ℝ) (hw : ∀ r, 0 ≤ weights r)
    (hsumw : ∑ r, weights r = 1) (p q : R → Profile ell)
    (leftGrade rightGrade : R → ℕ) (parentGrade : ℕ)
    (hgrade : ∀ r, leftGrade r + rightGrade r = parentGrade)
    (hp : ∀ r (x : CompleteWord ell),
      (∑ i, (x i).val) ≠ leftGrade r → (p r).probability x = 0)
    (hq : ∀ r (y : CompleteWord ell),
      (∑ i, (y i).val) ≠ rightGrade r → (q r).probability y = 0) :
    ∃ beta : Profile (ell + 1),
      (∀ w, beta.probability w =
        mixedProbability weights
          (fun r ↦ concatenatedProbability hell (p r).probability (q r).probability) w) ∧
      (∀ w : CompleteWord (ell + 1),
        (∑ i, (w i).val) ≠ parentGrade → beta.probability w = 0) := by
  obtain ⟨beta, hbeta, _, _, _⟩ :=
    mme_complete_split_mixture_concatenated_profile ell hell weights hw hsumw p q
  refine ⟨beta, hbeta, ?_⟩
  intro w hparent
  let e := completeWordSplitEquiv ell hell
  have hsplit : (∑ i, (w i).val) =
      (∑ i, ((e w).1 i).val) + ∑ i, ((e w).2 i).val := by
    have h := (mme_complete_split_literal_concatenation_grade
      ell hell (e w).1 (e w).2).2.2
    simpa only [Prod.mk.eta, e, Equiv.symm_apply_apply] using h
  rw [hbeta]
  unfold mixedProbability
  apply Finset.sum_eq_zero
  intro r _
  change weights r * ((p r).probability (e w).1 * (q r).probability (e w).2) = 0
  by_cases hleft : (∑ i, ((e w).1 i).val) = leftGrade r
  · have hright : (∑ i, ((e w).2 i).val) ≠ rightGrade r := by
      intro hright
      apply hparent
      calc
        (∑ i, (w i).val) =
            (∑ i, ((e w).1 i).val) + ∑ i, ((e w).2 i).val := hsplit
        _ = parentGrade := by rw [hleft, hright, hgrade]
    rw [hq r (e w).2 hright, mul_zero, mul_zero]
  · rw [hp r (e w).1 hleft, zero_mul, mul_zero]
