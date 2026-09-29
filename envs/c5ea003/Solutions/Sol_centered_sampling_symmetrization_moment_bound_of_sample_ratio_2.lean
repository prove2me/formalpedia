-- Prove2me | solution 2 for centered_sampling_symmetrization_moment_bound_of_sample_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T03:36:30.691551+00:00
-- url     : https://prove2.me/submissions/c8311c07-49da-42c5-8be0-44bacd399d14

import Theorems.Thm_centered_sampling_jensen_independent_copy_moment_bound_of_sample_ratio
import Theorems.Thm_centered_sampling_independent_copy_rademacher_symmetrization_of_sample_ratio
import Theorems.Thm_rademacher_sampled_difference_moment_le_single_sample_moment_of_sample_ratio

open MatrixCompletion
open scoped BigOperators Classical

/-- `centered_sampling_symmetrization_moment_bound_of_sample_ratio`.
Composes the three symmetrization steps (Candès–Recht 2009/2012, §6.1):
  (1) Jensen independent-copy moment bound `E‖F‖^q ≤ E_pair‖F(Ω)−F(Ω')‖^q`
      (`centered_sampling_jensen_independent_copy_moment_bound_of_sample_ratio`);
  (2) Rademacher symmetrization `E_pair‖F(Ω)−F(Ω')‖^q ≤ E_pair E_ε‖A(Ω,ε)−A(Ω',ε)‖^q`
      (`centered_sampling_independent_copy_rademacher_symmetrization_of_sample_ratio`);
  (3) triangle `E_pair E_ε‖A(Ω,ε)−A(Ω',ε)‖^q ≤ Csym^q · E_Ω E_ε‖A(Ω,ε)‖^q`
      (`rademacher_sampled_difference_moment_le_single_sample_moment_of_sample_ratio`).
The `Csym` is inherited from step (3). -/
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
  obtain ⟨Csym, hCsym, hsym⟩ :=
    rademacher_sampled_difference_moment_le_single_sample_moment_of_sample_ratio
  refine ⟨Csym, hCsym, ?_⟩
  intro n₁ n₂ m q X hn₁ hn₂ hm hq
  have h1 := centered_sampling_jensen_independent_copy_moment_bound_of_sample_ratio
    n₁ n₂ m q X hn₁ hn₂ hm hq
  have h2 := centered_sampling_independent_copy_rademacher_symmetrization_of_sample_ratio
    n₁ n₂ m q X hn₁ hn₂ hm hq
  have h3 := hsym n₁ n₂ m q X hn₁ hn₂ hm hq
  exact le_trans h1 (le_trans h2 h3)
