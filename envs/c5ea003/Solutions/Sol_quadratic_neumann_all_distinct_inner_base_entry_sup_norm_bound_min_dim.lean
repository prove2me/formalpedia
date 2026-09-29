-- Prove2me | solution 1 for quadratic_neumann_all_distinct_inner_base_entry_sup_norm_bound_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-26T21:59:35.66601+00:00
-- url     : https://prove2.me/submissions/82c36ec4-1305-4d3e-9efd-759bdeb922c2

import Theorems.Thm_linear_neumann_off_diagonal_coefficient_base_entry_sup_norm_bound_min_dim
import Theorems.Thm_quadratic_neumann_all_distinct_inner_base_norms_le_linear_offdiag_base

open MatrixCompletion
open scoped Classical BigOperators

theorem solution :
    ∃ Centry : ℝ, 0 < Centry ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        ∀ w1 w2 : Fin n₁ × Fin n₂,
          entrySupNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Centry * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  obtain ⟨Centry, hCentry, hlinear⟩ :=
    linear_neumann_off_diagonal_coefficient_base_entry_sup_norm_bound_min_dim
  refine ⟨Centry, hCentry, ?_⟩
  intro n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 w1 w2
  exact le_trans
    (quadratic_neumann_all_distinct_inner_base_norms_le_linear_offdiag_base S w1 w2).1
    (hlinear n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 w2)
