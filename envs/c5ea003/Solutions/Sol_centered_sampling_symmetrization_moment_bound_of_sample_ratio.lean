-- Prove2me | solution 1 for centered_sampling_symmetrization_moment_bound_of_sample_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T23:11:33.963662+00:00
-- url     : https://prove2.me/submissions/6ce6a728-418f-47d5-97ea-1239617f8504

import Theorems.Thm_centered_sampling_jensen_independent_copy_moment_bound_of_sample_ratio
import Theorems.Thm_centered_sampling_independent_copy_rademacher_symmetrization_of_sample_ratio
import Theorems.Thm_rademacher_sampled_difference_moment_le_single_sample_moment_of_sample_ratio

open MatrixCompletion

/-!
Source: Candes-Recht 2008, PDF p. 24, Section 6.1, equation (6.5) and the
following Jensen/Rademacher symmetrization paragraph.  The proof first applies
Jensen to compare `E ||S||^q` with an independent-copy difference, then uses the
Rademacher symmetry of `δ - δ'`, and finally applies the triangle inequality to
bound the signed difference by one signed sampled copy.

Reduction: this sample-ratio parent uses sample-ratio-safe children throughout.
The hypotheses `0 < n₁`, `0 < n₂`, and `m ≤ n₁*n₂` are passed to the Jensen,
Rademacher-symmetrization, and triangle/Minkowski children, so the reduction
never relies on signed Bernoulli weights outside `p ∈ [0,1]`.
-/
theorem solution :
    ∃ Csym : ℝ, 0 < Csym ∧
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          Csym ^ q *
            bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                rademacherExpectation
                  (fun eps =>
                    spectralNorm
                      (rademacherSampledMatrix Omega eps
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) := by
  rcases rademacher_sampled_difference_moment_le_single_sample_moment_of_sample_ratio with
    ⟨Csym, hCsym, hTriangle⟩
  refine ⟨Csym, hCsym, ?_⟩
  intro n₁ n₂ m q X hn₁ hn₂ hm hq
  have hIndependentCopy :=
    centered_sampling_jensen_independent_copy_moment_bound_of_sample_ratio
      n₁ n₂ m q X hn₁ hn₂ hm hq
  have hRademacherDifference :=
    centered_sampling_independent_copy_rademacher_symmetrization_of_sample_ratio
      n₁ n₂ m q X hn₁ hn₂ hm hq
  have hOneCopy :=
    hTriangle n₁ n₂ m q X hn₁ hn₂ hm hq
  exact le_trans hIndependentCopy (le_trans hRademacherDifference hOneCopy)
