-- Prove2me | solution 1 for fixed_matrix_centered_sampling_spectral_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:49:44.814124+00:00
-- url     : https://prove2.me/submissions/c7bf86f8-d43d-4a11-b821-15ca98746c9d

import Theorems.Thm_fixed_matrix_centered_sampling_log_moment_bound
import Theorems.Thm_fixed_matrix_centered_sampling_tail_from_log_moment_bound

open MatrixCompletion

/-- Decompose Candes-Recht Theorem 6.3 into its log-moment estimate and the
Markov tail conversion. -/
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              CenteredSamplingSpectralBound Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
                (C * Real.sqrt
                  ((β * (↑(max n₁ n₂)) *
                      Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entrySupNorm X)) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases fixed_matrix_centered_sampling_log_moment_bound with
    ⟨Cmoment, hCmoment, hMoment⟩
  rcases fixed_matrix_centered_sampling_tail_from_log_moment_bound
      Cmoment hCmoment with
    ⟨Ctail, hCtail, hTail⟩
  refine ⟨Ctail, hCtail, ?_⟩
  intro β hβ n₁ n₂ m X hn₁ hn₂ hm hSample
  exact hTail β hβ n₁ n₂ m X hn₁ hn₂ hm hSample
    (hMoment β hβ n₁ n₂ m X hn₁ hn₂ hm hSample)

