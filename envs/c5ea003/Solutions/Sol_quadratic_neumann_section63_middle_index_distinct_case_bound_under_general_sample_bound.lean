-- Prove2me | solution 1 for quadratic_neumann_section63_middle_index_distinct_case_bound_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T18:50:33.046363+00:00
-- url     : https://prove2.me/submissions/31754bf5-4cf6-4fef-b0fd-7ccd276df2af

import Theorems.Thm_quadratic_neumann_section63_middle_index_distinct_centered_case_bound_under_general_sample_bound
import Theorems.Thm_quadratic_neumann_section63_middle_index_distinct_mean_case_bound_under_general_sample_bound
import Theorems.Thm_quadratic_neumann_middle_index_distinct_contribution_bound_from_centered_and_mean_bounds_at_scale
import Theorems.Thm_bernoulli_event_intersection_probability_from_lower_bounds
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Tactic

open MatrixCompletion

/-!
Source: Candes-Recht 2008, Section 6.3, PDF pp. 32--33.

This is the `ω₁ = ω₃ ≠ ω₂` case in the five-way partition (6.20).  The paper
rewrites the term with
`ξ_{ω₁}^2 = (1 - 2p) ξ_{ω₁} + p(1-p)`, treats the first subterm by a
decoupled Bernstein estimate for the auxiliary coefficients followed by
Theorem 6.3, and treats the second subterm by the corresponding deterministic
coefficient estimate.  This sketch only performs the formal assembly:
intersect the centered and mean high-probability events and apply the
deterministic recombination theorem for the split.
-/
theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannMiddleIndexDistinctContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 C *
                   ((μ₀ ^ 2 * μ₁) *
                      Real.sqrt ((N * R * (β * logN)) / Mobs) *
                        ((N * R) / Mobs) ^ 2 +
                    μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
                    Real.sqrt (β * logN) *
                        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                          (μ₀ ^ 2 * R) +
                    Real.rpow
                      ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
                      ((3 : ℝ) / 2)))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases
      quadratic_neumann_section63_middle_index_distinct_centered_case_bound_under_general_sample_bound with
    ⟨Ccent, ccent, hCcent, hccent, hCentered⟩
  rcases
      quadratic_neumann_section63_middle_index_distinct_mean_case_bound_under_general_sample_bound with
    ⟨Cmean, cmean, hCmean, hcmean, hMean⟩
  refine ⟨Ccent + Cmean, ccent + cmean,
    add_pos hCcent hCmean, add_pos hccent hcmean, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let scale : ℝ :=
    (let N : ℝ := ↑(max n₁ n₂)
     let R : ℝ := (r : ℝ)
     let Mobs : ℝ := (m : ℝ)
     let logN : ℝ := Real.log N
     ((μ₀ ^ 2 * μ₁) *
        Real.sqrt ((N * R * (β * logN)) / Mobs) *
          ((N * R) / Mobs) ^ 2 +
      μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
      Real.sqrt (β * logN) *
          Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
            (μ₀ ^ 2 * R) +
      Real.rpow
        ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
        ((3 : ℝ) / 2)))
  have hCcent_le : Ccent ≤ C' := by linarith
  have hCmean_le : Cmean ≤ C' := by linarith
  have hCenteredProb :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm
              (quadraticNeumannMiddleIndexDistinctCenteredContribution Omega S p) ≤
              Ccent * scale) ≥
        1 - ccent * Real.rpow (↑(max n₁ n₂)) (-β) := by
    simpa [p, scale] using
      hCentered C' hCcent_le β hβ n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hMeanProb :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm
              (quadraticNeumannMiddleIndexDistinctMeanContribution Omega S p) ≤
              Cmean * scale) ≥
        1 - cmean * Real.rpow (↑(max n₁ n₂)) (-β) := by
    simpa [p, scale] using
      hMean C' hCmean_le β hβ n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hpNonneg, hpLeOne⟩
  have hIntersection :=
    bernoulli_event_intersection_probability_from_lower_bounds
      p ccent cmean (Real.rpow (↑(max n₁ n₂)) (-β))
      (fun Omega =>
        spectralNorm
          (quadraticNeumannMiddleIndexDistinctCenteredContribution Omega S p) ≤
          Ccent * scale)
      (fun Omega =>
        spectralNorm
          (quadraticNeumannMiddleIndexDistinctMeanContribution Omega S p) ≤
          Cmean * scale)
      hpNonneg hpLeOne hCenteredProb hMeanProb
  have hMono :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm
                (quadraticNeumannMiddleIndexDistinctCenteredContribution Omega S p) ≤
              Ccent * scale ∧
            spectralNorm
                (quadraticNeumannMiddleIndexDistinctMeanContribution Omega S p) ≤
              Cmean * scale) ≤
        bernoulliEventProb p
          (fun Omega =>
            spectralNorm
              (quadraticNeumannMiddleIndexDistinctContribution Omega S p) ≤
              (Ccent + Cmean) * scale) :=
    bernoulli_event_probability_mono p
      (fun Omega =>
        spectralNorm
            (quadraticNeumannMiddleIndexDistinctCenteredContribution Omega S p) ≤
          Ccent * scale ∧
        spectralNorm
            (quadraticNeumannMiddleIndexDistinctMeanContribution Omega S p) ≤
          Cmean * scale)
      (fun Omega =>
        spectralNorm
          (quadraticNeumannMiddleIndexDistinctContribution Omega S p) ≤
          (Ccent + Cmean) * scale)
      hpNonneg hpLeOne
      (by
        intro Omega hGood
        exact
          quadratic_neumann_middle_index_distinct_contribution_bound_from_centered_and_mean_bounds_at_scale
            S Omega p Ccent Cmean scale hGood.1 hGood.2)
  simpa [p, scale] using le_trans hIntersection hMono
