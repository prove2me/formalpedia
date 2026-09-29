-- Prove2me | solution 1 for centered_sampling_log_moment_scale_absorption
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T02:22:47.675581+00:00
-- url     : https://prove2.me/submissions/26593522-306f-4b4a-9854-a3c2f32aec89

import Theorems.Thm_centered_sampling_log_moment_scale_absorption
import Theorems.Thm_centered_sampling_log_moment_khintchine_scale_from_symmetrization_and_rademacher
import Theorems.Thm_centered_sampling_log_moment_beta_scale_from_khintchine_scale

open MatrixCompletion

/-- Split the Section 6.1 scale absorption into the expectation-transitivity
step from symmetrization/Rademacher bounds and the algebraic absorption
`q ≤ 2 β log n`. -/
theorem solution
    (Csym Crad : ℝ) :
    0 < Csym →
    0 < Crad →
    ∃ Cmoment : ℝ, 0 < Cmoment ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) →
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
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              rademacherExpectation
                (fun eps =>
                  spectralNorm
                    (rademacherSampledMatrix Omega eps
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) ≤
          (Crad * Real.sqrt
            (((q : ℝ) * (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Cmoment * Real.sqrt
            ((β * (↑(max n₁ n₂)) *
                Real.log (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q := by
  intro hCsym hCrad
  rcases
      centered_sampling_log_moment_khintchine_scale_from_symmetrization_and_rademacher
        Csym Crad hCsym hCrad with
    ⟨Cq, hCq, hKhintchineScale⟩
  rcases centered_sampling_log_moment_beta_scale_from_khintchine_scale
      Cq hCq with
    ⟨Cmoment, hCmoment, hBetaScale⟩
  refine ⟨Cmoment, hCmoment, ?_⟩
  intro β hβ n₁ n₂ m q X hn₁ hn₂ hm hSample
    hqOne hqLogLower hqLogUpper hSymm hRad
  have hQScale :=
    hKhintchineScale n₁ n₂ m q X hqOne hSymm hRad
  exact hBetaScale β hβ n₁ n₂ m q X
    hn₁ hn₂ hm hSample hqOne hqLogLower hqLogUpper hQScale

