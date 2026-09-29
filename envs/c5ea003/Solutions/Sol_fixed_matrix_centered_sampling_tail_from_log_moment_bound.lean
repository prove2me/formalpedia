-- Prove2me | solution 1 for fixed_matrix_centered_sampling_tail_from_log_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T12:58:19.172805+00:00
-- url     : https://prove2.me/submissions/42ecdffb-5bfc-4df0-9092-09cc4ad6c79b

import Theorems.Thm_fixed_matrix_centered_sampling_markov_tail_from_q_moment_bound_of_nonneg_threshold
import Theorems.Thm_fixed_matrix_log_moment_scale_absorbs_markov_failure_factor
import Mathlib.Tactic

open MatrixCompletion

private lemma entrySupNorm_nonneg_of_pos
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    0 ≤ entrySupNorm X := by
  let i0 : Fin n₁ := ⟨0, hn₁⟩
  let j0 : Fin n₂ := ⟨0, hn₂⟩
  exact le_trans (abs_nonneg (X i0 j0))
    (le_trans
      (le_ciSup
        (Finite.bddAbove_range (fun j : Fin n₂ => |X i0 j|)) j0)
      (le_ciSup
        (Finite.bddAbove_range
          (fun i : Fin n₁ => ⨆ j : Fin n₂, |X i j|)) i0))

/-- Repaired Markov/log-moment tail conversion.  The old reduction used a raw
Markov theorem without the required nonnegative-threshold hypothesis; here the
threshold is visibly nonnegative because it is a positive constant times a
square root times an entry sup norm. -/
theorem solution
    (Cmoment : ℝ) :
    0 < Cmoment →
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        (∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                spectralNorm
                  (centeredSamplingFluctuation Omega
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
            (Cmoment * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm X) ^ q) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              CenteredSamplingSpectralBound Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
                (Ctail * Real.sqrt
                  ((β * (↑(max n₁ n₂)) *
                      Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entrySupNorm X)) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCmoment
  rcases fixed_matrix_log_moment_scale_absorbs_markov_failure_factor
      Cmoment hCmoment with
    ⟨Ctail, hCtail, hAbsorb⟩
  refine ⟨Ctail, hCtail, ?_⟩
  intro β hβ n₁ n₂ m X hn₁ hn₂ hm hSample hMoment
  rcases hMoment with ⟨q, hq, hqLog, hMomentBound⟩
  let threshold : ℝ :=
    Ctail * Real.sqrt
      ((β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂))) /
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
      entrySupNorm X
  have hThresholdNonneg : 0 ≤ threshold := by
    dsimp [threshold]
    exact mul_nonneg
      (mul_nonneg (le_of_lt hCtail) (Real.sqrt_nonneg _))
      (entrySupNorm_nonneg_of_pos X hn₁ hn₂)
  have hScaledMoment :
      bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            spectralNorm
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
        threshold ^ q *
          Real.rpow (↑(max n₁ n₂)) (-β) := by
    exact le_trans hMomentBound
      (by
        dsimp [threshold]
        exact hAbsorb β hβ n₁ n₂ m q X hn₁ hn₂ hm hq hqLog hSample)
  exact
    fixed_matrix_centered_sampling_markov_tail_from_q_moment_bound_of_nonneg_threshold
      β threshold hβ hThresholdNonneg n₁ n₂ m q X hn₁ hn₂ hm hq
      hScaledMoment
