-- Prove2me | solution 1 for quadratic_neumann_all_distinct_inner_base_frobenius_norm_bound_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-26T22:01:24.900319+00:00
-- url     : https://prove2.me/submissions/7b304766-2ae7-4a11-87b9-655d05410243

import Theorems.Thm_linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min_dim
import Theorems.Thm_quadratic_neumann_all_distinct_inner_base_norms_le_linear_offdiag_base

open MatrixCompletion
open scoped Classical BigOperators

theorem solution :
    ∃ Cfro : ℝ, 0 < Cfro ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        ∀ w1 w2 : Fin n₁ × Fin n₂,
          frobeniusNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt
                  (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  obtain ⟨Cfro, hCfro, hlinear⟩ :=
    linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min_dim
  refine ⟨Cfro, hCfro, ?_⟩
  intro n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 w1 w2
  exact le_trans
    (quadratic_neumann_all_distinct_inner_base_norms_le_linear_offdiag_base S w1 w2).2
    (hlinear n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 w2)
