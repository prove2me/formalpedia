-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_centered_coefficient_pointwise_tail_from_kernel_square_base_bounds_min_dim
-- name    : quadratic_neumann_middle_index_distinct_centered_coefficient_pointwise_tail_from_kernel_square_base_bounds_min_dim
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-23T06:10:00.89675+00:00
-- url     : https://prove2.me/theorems/8e073a1f-5ace-42ca-bf12-b03edc18e85a
-- statement:
--   The $(r/\min)$-form pointwise tail bound for the **centered** Neumann coefficient matrix of the middle-index-distinct quadratic term in the Candès–Recht exact matrix completion analysis. The centered coefficient equals a sign factor times the entry-sum of the centered sampling fluctuation of the off-diagonal kernel-square base matrix. Given the corrected min-dimension base bounds ($\mathrm{entrySup}\le C_{\mathrm{entry}}\mu_0^2(r/\min)^2$, $\mathrm{frob}\le C_{\mathrm{fro}}\mu_0^{3/2}(r/\min)^{3/2}$) and the density floor $m\ge\lambda\mu_0^{4/3}\max\,r^{4/3}\beta\log\max$, with probability at least $1-c_{\mathrm{point}}\max^{-\beta}$ the centered coefficient is bounded by $C_{\mathrm{point}}\lambda^{-1}$. Corrected min-dimension sibling of the proved max-form centered pointwise tail; conclusion unchanged. Reduction children: the parametric scalar-Bernstein engine, the signed kernel-square Bernstein scale-compatibility lemma (signed_kernel_square_bernstein_scale_compatibility_from_a0_sample_bound), the Bernoulli event monotonicity lemma, plus the solution-local min-scale absorption identity. Source: Candès–Recht 2009 (arXiv:0805.4471) §6.2 scalar Bernstein bound; min-cancel + density-floor absorption.
-- source:
--   Candès–Recht 2009, arXiv:0805.4471, §6.2 (scalar Bernstein)

import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MatrixCompletion
open scoped Classical BigOperators

theorem quadratic_neumann_middle_index_distinct_centered_coefficient_pointwise_tail_from_kernel_square_base_bounds_min_dim
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
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
        ∀ w1 : Fin n₁ × Fin n₂,
        (∀ Omega2 : Finset (Fin n₁ × Fin n₂),
          quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1.1 w1.2 =
            signMatrix S w1.1 w1.2 *
              matrixEntrySum
                (centeredSamplingFluctuation Omega2
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                  (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1))) →
        entrySupNorm
            (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
          Centry * μ₀ ^ 2 *
            (((r : ℝ) / (↑(min n₁ n₂))) ^ 2) →
        frobeniusNorm
            (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
          Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
            Real.rpow ((r : ℝ) / (↑(min n₁ n₂))) ((3 : ℝ) / 2) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              |quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1.1 w1.2| ≤
                Cpoint * Real.rpow lam (-1)) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) := by sorry
