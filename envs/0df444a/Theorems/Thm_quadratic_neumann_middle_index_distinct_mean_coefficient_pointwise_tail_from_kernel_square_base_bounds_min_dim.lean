-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_mean_coefficient_pointwise_tail_from_kernel_square_base_bounds_min_dim
-- name    : quadratic_neumann_middle_index_distinct_mean_coefficient_pointwise_tail_from_kernel_square_base_bounds_min_dim
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-23T06:09:41.586279+00:00
-- url     : https://prove2.me/theorems/5b10f89f-99fe-4ea5-a3cb-a9abb58b2555
-- statement:
--   The $(r/\min)$-form pointwise tail bound for the **mean** Neumann coefficient of the middle-index-distinct quadratic term in the Candès–Recht exact matrix completion analysis. Given off-diagonal kernel-square base bounds in the corrected min-dimension scaling ($\mathrm{entrySup} \le C_{\mathrm{entry}}\mu_0^2 (r/\min(n_1,n_2))^2$ and $\mathrm{frob}\le C_{\mathrm{fro}}\mu_0^{3/2}(r/\min(n_1,n_2))^{3/2}$), under the sampling density floor $m\ge \lambda\mu_0^{4/3}\max(n_1,n_2) r^{4/3}\beta\log\max(n_1,n_2)$, the mean coefficient satisfies a scalar-Bernstein pointwise tail: with probability at least $1-c_{\mathrm{point}}\max(n_1,n_2)^{-\beta}$, $|\mathrm{mean}|\le C_{\mathrm{point}}\sqrt{\beta\log\max(n_1,n_2)}\,(\mu_0\max(n_1,n_2)r/m)^{3/2}$. This is the corrected min-dimension sibling of the proved max-form pointwise tail; the conclusion scale is unchanged. Reduction children: the parametric scalar-Bernstein engine (scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales), the Bernoulli event monotonicity lemma (bernoulli_event_probability_mono), plus a solution-local min-scale absorption identity. Source: Candès–Recht 2009 (arXiv:0805.4471) §6.2 scalar Bernstein bound; the min-cancel $m/(\min\cdot\max)=p\le 1$ (sub-Gaussian term) and the density floor $\min\ge\mu_0 r\beta\log\max$ (sub-exponential term).
-- source:
--   Candès–Recht 2009, arXiv:0805.4471, §6.2 (scalar Bernstein)

import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MatrixCompletion
open scoped Classical BigOperators

theorem quadratic_neumann_middle_index_distinct_mean_coefficient_pointwise_tail_from_kernel_square_base_bounds_min_dim
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
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          quadraticMiddleIndexDistinctMeanCoefficient Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
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
            (fun Omega =>
              |quadraticMiddleIndexDistinctMeanCoefficient Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1| ≤
                Cpoint *
                  Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
                    Real.rpow
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                      ((3 : ℝ) / 2)) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) := by sorry
