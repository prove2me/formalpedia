-- Prove2me | solution 1 for linear_neumann_off_diagonal_coefficient_bound_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T10:49:07.486956+00:00
-- url     : https://prove2.me/submissions/49859cc3-6502-449f-ad33-2c8be226cdce

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_entry_as_centered_scalar_fluctuation
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_base_entry_sup_norm_bound_min_dim
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min_dim
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_bound_from_lemma66_min_dim_base_bounds

open MatrixCompletion

open MatrixCompletion

/-!
Source: Candès--Recht 2008, Section 6.2, PDF pp. 27--29, equations
(6.13)--(6.17), with the rectangular convention after equations (6.2)--(6.4)
and the Theorem 1.3 sample lower bound in equation (1.9).

This reduction is the corrected general-sample replacement for the old
`small_with_lambda` coefficient route.  It plugs the already-proved
rectangular deterministic base estimates into the exact Lemma 6.6 scalar
Bernstein/union-bound statement.
-/
theorem solution :
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ C' : ℝ, Ccoef ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              LinearNeumannOffDiagonalCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * μ₁ *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                          (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases linear_neumann_off_diagonal_coefficient_base_entry_sup_norm_bound_min_dim with
    ⟨Centry, hCentry_pos, hEntry⟩
  rcases linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min_dim with
    ⟨Cfro, hCfro_pos, hFrob⟩
  rcases
      linear_neumann_off_diagonal_coefficient_bound_from_lemma66_min_dim_base_bounds
        Centry Cfro hCentry_pos hCfro_pos with
    ⟨Ccoef, ccoef, hCcoef, hccoef, hLemma66⟩
  refine ⟨Ccoef, ccoef, hCcoef, hccoef, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hRep :
      ∀ (Omega2 : Finset (Fin n₁ × Fin n₂))
          (w : Fin n₁ × Fin n₂),
        linearNeumannOffDiagonalCoefficientMatrix Omega2 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w.1 w.2 =
          matrixEntrySum
            (centeredSamplingFluctuation Omega2
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (linearNeumannOffDiagonalCoefficientBaseMatrix S w)) := by
    intro Omega2 w
    exact linear_neumann_off_diagonal_coefficient_entry_as_centered_scalar_fluctuation
      Omega2 S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w
  exact hLemma66 C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower hRep
    (hEntry n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1)
    (hFrob n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1)

