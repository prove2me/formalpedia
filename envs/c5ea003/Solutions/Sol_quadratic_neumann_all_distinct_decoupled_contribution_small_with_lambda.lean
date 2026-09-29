-- Prove2me | solution 1 for quadratic_neumann_all_distinct_decoupled_contribution_small_with_lambda
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:49:50.171227+00:00
-- url     : https://prove2.me/submissions/1bff0e83-aa35-4554-9e06-3e98f48a47e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_quadratic_neumann_all_distinct_middle_coefficients_small_with_lambda
import Theorems.Thm_quadratic_neumann_all_distinct_decoupled_from_middle_coefficient_bound

open MatrixCompletion

/-- Prove the decoupled all-distinct estimate by first controlling the middle
coefficients `H_{ω₁}` and then applying the final centered sampling step in the
outer `ω₁` variable. -/
theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
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
        bernoulliTripleEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega2 Omega3 =>
              spectralNorm
                (quadraticNeumannAllDistinctDecoupledContribution
                  Omega1 Omega2 Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                C * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases quadratic_neumann_all_distinct_middle_coefficients_small_with_lambda with
    ⟨Cmid, cmid, hCmid, hcmid, hMiddle⟩
  rcases quadratic_neumann_all_distinct_decoupled_from_middle_coefficient_bound with
    ⟨Couter, couter, hCouter, hcouter, hOuter⟩
  refine ⟨Couter * Cmid, couter + cmid,
    mul_pos hCouter hCmid, add_pos hcouter hcmid, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hMiddleProb :=
    hMiddle β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  exact hOuter β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    Cmid cmid hCmid hcmid hMiddleProb

