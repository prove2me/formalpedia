-- Prove2me | solution 1 for quadratic_neumann_all_distinct_triple_probability_from_middle_and_outer_conditional_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:25:07.761633+00:00
-- url     : https://prove2.me/submissions/a0e54ba7-4251-47ed-8ed1-08678d789b6b

import Theorems.Thm_bernoulli_triple_event_probability_from_pair_marginal_and_conditional_lower_bounds_of_nonneg
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Specialize the reusable three-copy Bernoulli product lift to the final
outer step of the all-distinct decoupled quadratic term. -/
theorem solution
    (Ccond ccond : ℝ) :
    0 < Ccond → 0 < ccond →
    ∃ Couter couter : ℝ, 0 < Couter ∧ 0 < couter ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ Cmid cmid : ℝ, 0 < Cmid → 0 < cmid →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 Omega3 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Cmid * Real.rpow lam (-1))) ≥
          1 - cmid * Real.rpow (↑(max n₁ n₂)) (-β) →
        (∀ Omega2 Omega3 : Finset (Fin n₁ × Fin n₂),
          QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (Cmid * Real.rpow lam (-1)) →
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega1 =>
                spectralNorm
                  (quadraticNeumannAllDistinctDecoupledContribution
                    Omega1 Omega2 Omega3 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                  (Ccond * Cmid) * Real.rpow lam (-((3 : ℝ) / 2))) ≥
            1 - ccond * Real.rpow (↑(max n₁ n₂)) (-β)) →
        bernoulliTripleEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega2 Omega3 =>
              spectralNorm
                (quadraticNeumannAllDistinctDecoupledContribution
                  Omega1 Omega2 Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (Couter * Cmid) * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - (couter + cmid) *
            Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCcond hccond
  refine ⟨Ccond, ccond, hCcond, hccond, ?_⟩
  intro β lam _hβ _hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ _hr hm _hμ₀ _hμ₁ _hA0 _hA1 _hmLower
    Cmid cmid _hCmid _hcmid hMiddleProb hCondProb
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hp : 0 ≤ p ∧ p ≤ 1 := by
    exact sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hFailureNonneg :
      0 ≤ ccond * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have hmax_pos_nat : 0 < max n₁ n₂ :=
      lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
    have hmax_pos : 0 < (↑(max n₁ n₂) : ℝ) := by
      exact_mod_cast hmax_pos_nat
    exact mul_nonneg (le_of_lt hccond)
      (le_of_lt (Real.rpow_pos_of_pos hmax_pos (-β)))
  exact
    bernoulli_triple_event_probability_from_pair_marginal_and_conditional_lower_bounds_of_nonneg
      p cmid ccond (Real.rpow (↑(max n₁ n₂)) (-β))
      (fun Omega2 Omega3 =>
        QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p
          (Cmid * Real.rpow lam (-1)))
      (fun Omega1 Omega2 Omega3 =>
        spectralNorm
          (quadraticNeumannAllDistinctDecoupledContribution
            Omega1 Omega2 Omega3 S p) ≤
          (Ccond * Cmid) * Real.rpow lam (-((3 : ℝ) / 2)))
      hp.1 hp.2 hFailureNonneg hMiddleProb hCondProb
