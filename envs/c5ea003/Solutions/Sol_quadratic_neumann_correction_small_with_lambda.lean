-- Prove2me | solution 1 for quadratic_neumann_correction_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T03:55:14.113683+00:00
-- url     : https://prove2.me/submissions/f3591b5d-3981-4ef7-b6d3-a06cae3736e4

import Theorems.Thm_quadratic_neumann_all_equal_contribution_small_with_lambda
import Theorems.Thm_quadratic_neumann_first_index_distinct_contribution_small_with_lambda
import Theorems.Thm_quadratic_neumann_middle_index_distinct_contribution_small_with_lambda
import Theorems.Thm_quadratic_neumann_last_index_distinct_contribution_small_with_lambda
import Theorems.Thm_quadratic_neumann_all_distinct_contribution_small_with_lambda
import Theorems.Thm_quadratic_neumann_correction_from_index_partition_bounds
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Source: Candes-Recht 2008, PDF pp. 20-21 and 30-34, Lemma 4.6 and the
five-way index partition in equation (6.20), followed by the bounds for each
case through the conclusion on PDF p. 34.

Decompose Candes-Recht Lemma 4.6 by the five index-coincidence cases in
equation (6.20). -/
theorem solution :
    ∃ C₂ c₂ : ℝ, 0 < C₂ ∧ 0 < c₂ ∧
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
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              NeumannCertificateTermSpectralBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 2
                (C₂ * Real.rpow lam (-((3 : ℝ) / 2)))) ≥
          1 - c₂ * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases quadratic_neumann_all_equal_contribution_small_with_lambda with
    ⟨C0, c0, hC0, hc0, h0⟩
  rcases quadratic_neumann_first_index_distinct_contribution_small_with_lambda with
    ⟨C123, c123, hC123, hc123, h123⟩
  rcases quadratic_neumann_middle_index_distinct_contribution_small_with_lambda with
    ⟨C132, c132, hC132, hc132, h132⟩
  rcases quadratic_neumann_last_index_distinct_contribution_small_with_lambda with
    ⟨C112, c112, hC112, hc112, h112⟩
  rcases quadratic_neumann_all_distinct_contribution_small_with_lambda with
    ⟨Call, call, hCall, hcall, hall⟩
  refine ⟨(((C0 + C123) + C132) + C112) + Call,
    (((c0 + c123) + c132) + c112) + call, ?_, ?_, ?_⟩
  · exact add_pos (add_pos (add_pos (add_pos hC0 hC123) hC132) hC112) hCall
  · exact add_pos (add_pos (add_pos (add_pos hc0 hc123) hc132) hc112) hcall
  · intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
      ⟨hpNonneg, hpLeOne⟩
    have h0Prob :=
      h0 β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have h123Prob :=
      h123 β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have h132Prob :=
      h132 β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have h112Prob :=
      h112 β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have hallProb :=
      hall β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    exact quadratic_neumann_correction_from_index_partition_bounds S
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
      C0 C123 C132 C112 Call c0 c123 c132 c112 call β lam
      hpNonneg hpLeOne
      hc0 hc123 hc132 hc112 hcall h0Prob h123Prob h132Prob h112Prob hallProb
