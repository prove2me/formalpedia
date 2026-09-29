-- Prove2me | solution 1 for centered_sampling_log_moment_khintchine_scale_from_symmetrization_and_rademacher
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T04:48:34.829663+00:00
-- url     : https://prove2.me/submissions/cd3ac9da-01b5-45aa-aa92-a7c709a7b6c4

import Theorems.Thm_centered_sampling_log_moment_khintchine_scale_from_symmetrization_and_rademacher
import Theorems.Thm_bernoulli_moment_bound_from_symmetrization_and_auxiliary_moment_bound

open MatrixCompletion

/-- Apply the abstract moment-transitivity lemma to the centered-sampling
moment and the Rademacher auxiliary moment. -/
theorem solution
    (Csym Crad : ℝ) :
    0 < Csym →
    0 < Crad →
    ∃ Cq : ℝ, 0 < Cq ∧
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        1 ≤ q →
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
          (Cq * Real.sqrt
            (((q : ℝ) * (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q := by
  intro hCsym hCrad
  rcases bernoulli_moment_bound_from_symmetrization_and_auxiliary_moment_bound
      Csym Crad hCsym hCrad with
    ⟨Cq, hCq, hMoment⟩
  refine ⟨Cq, hCq, ?_⟩
  intro n₁ n₂ m q X hq hSymm hRad
  have hRad' :
      bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            rademacherExpectation
              (fun eps =>
                spectralNorm
                  (rademacherSampledMatrix Omega eps
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) ≤
        (Crad *
          (Real.sqrt
            (((q : ℝ) * (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X)) ^ q := by
    simpa [mul_assoc] using hRad
  have h :=
    hMoment
    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
    (Real.sqrt
      (((q : ℝ) * (↑(max n₁ n₂))) /
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
      entrySupNorm X)
    q
    (fun Omega =>
      spectralNorm
        (centeredSamplingFluctuation Omega
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)
    (fun Omega =>
      rademacherExpectation
        (fun eps =>
          spectralNorm
            (rademacherSampledMatrix Omega eps
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q))
    hq hSymm hRad'
  simpa [mul_assoc] using h

