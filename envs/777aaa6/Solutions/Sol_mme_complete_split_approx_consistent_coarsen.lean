-- Prove2me | solution 1 for mme_complete_split_approx_consistent_coarsen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T21:29:25.697222+00:00
-- url     : https://prove2.me/submissions/4f110fdd-09ef-4515-85f0-4b786d72a589

import Definitions.Def_mme_complete_split_concatenation
import Mathlib.Tactic

open MME MME.CompleteSplit MME.DWZComponentRestriction BigOperators
open scoped NNReal

universe u v

set_option autoImplicit false
set_option warningAsError true

private theorem wordCount_eq_sum {ι : Type u} {ell N : ℕ}
    (label : ι → CompleteWord ell) (w : PowIndex ι N) (sigma : CompleteWord ell) :
    (wordCount label w sigma : ℝ) =
      ∑ r : Fin N, if label (PowIndex.get N w r) = sigma then (1 : ℝ) else 0 := by
  classical
  simp only [Finset.sum_boole, wordCount]

private theorem count_fiber {ι : Type u} {ell k N : ℕ}
    (label : ι → CompleteWord ell) (project : CompleteWord ell → CompleteWord k)
    (w : PowIndex ι N) (x : CompleteWord k) :
    (wordCount (project ∘ label) w x : ℝ) =
      ∑ sigma : CompleteWord ell,
        if project sigma = x then (wordCount label w sigma : ℝ) else 0 := by
  classical
  simp_rw [wordCount_eq_sum]
  simp_rw [Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Function.comp_apply]
  rw [Finset.sum_eq_single (label (PowIndex.get N w r))]
  · simp
  · intro sigma _ hne
    simp [Ne.symm hne]
  · simp

/-- Deterministic coarsening preserves approximate complete-profile
consistency, with an explicit finite alphabet loss in tolerance. -/
theorem solution {ι : Type u} {ell k N : ℕ}
    (label : ι → CompleteWord ell) (project : CompleteWord ell → CompleteWord k)
    (parent : Profile ell) (child : Profile k)
    (hmarginal : ∀ x, child.probability x =
      ∑ sigma : CompleteWord ell,
        if project sigma = x then parent.probability sigma else 0)
    (epsilon : ℝ≥0) (w : PowIndex ι N)
    (h : ApproxConsistent label parent epsilon w) :
    ApproxConsistent (project ∘ label) child
      ((Fintype.card (CompleteWord ell) : ℝ≥0) * epsilon) w := by
  classical
  intro x
  rw [count_fiber, hmarginal x, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ sigma : CompleteWord ell,
        |(if project sigma = x then (wordCount label w sigma : ℝ) else 0) -
          (N : ℝ) * (if project sigma = x then parent.probability sigma else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _sigma : CompleteWord ell, (N : ℝ) * (epsilon : ℝ) := by
      apply Finset.sum_le_sum
      intro sigma _
      by_cases hs : project sigma = x
      · simpa only [if_pos hs] using h sigma
      · simp only [if_neg hs, mul_zero, sub_zero, abs_zero]
        positivity
    _ = _ := by simp [mul_left_comm]
