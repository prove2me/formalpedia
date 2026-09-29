-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_mean_coefficients_from_kernel_square_base_bounds_min_dim_shifted
-- name    : quadratic_neumann_middle_index_distinct_mean_coefficients_from_kernel_square_base_bounds_min_dim_shifted
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-24T19:14:42.60778+00:00
-- url     : https://prove2.me/theorems/864d45fc-b9bd-41ef-b04f-51db4d4c13e4
-- statement:
--   This is a formal Lean bridge, not a theorem stated verbatim in Candes--Recht. It connects the source-backed pointwise mean-tail theorem `quadratic_neumann_middle_index_distinct_mean_coefficient_pointwise_tail_from_kernel_square_base_bounds_min_dim` with the source-backed shifted union-bound theorem `quadratic_neumann_middle_index_distinct_mean_coefficients_uniform_from_shifted_pointwise_tails` for the mean part of the middle-index-distinct quadratic Neumann term. Source location: Candes--Recht, *Exact matrix completion via convex optimization*, Section 6.3, proof of Lemma 4.6, PDF p. 30 equation (6.20) for the partition of the cubic Neumann sum, and PDF pp. 32--33 for the third term `omega_1 = omega_3 != omega_2`; the coordinate-union pattern follows the same Section 6.2 mechanism, PDF p. 29 after equation (6.17).
--
--   Let `M` be an `n_1 x n_2` rank-`r` matrix with SVD data `S` satisfying `A0(S, mu_0)` and `A1(S, mu_1)`. Here `mu_0` controls singular-vector coherence, `mu_1` controls the sign-matrix entry scale, `n = max(n_1,n_2)`, and `p = m/(n_1 n_2)`. In the Bernoulli model, `Omega` includes each coordinate independently with probability `p`, and `bernoulliEventProb(p, E)` is the probability of event `E`. The parameter `beta > 2` controls failure rate `n^{-beta}`, and `lambda >= 1` is the density slack parameter.
--
--   Assume the mean coefficient identity for every coordinate `w_1`, and assume the corrected min-dimension kernel-square base bounds
--   $$
--   \\|B_{w_1}\\|_\\infty \\le C_{\\rm entry}\\mu_0^2 (r/\\min(n_1,n_2))^2,
--   $$
--   and
--   $$
--   \\|B_{w_1}\\|_F \\le C_{\\rm fro}\\mu_0^{3/2}(r/\\min(n_1,n_2))^{3/2}.
--   $$
--   This bridge deliberately requires both the ordinary density floor
--   $$
--   m \\ge \\lambda\\,\\mu_0^{4/3}\\,n\\,r^{4/3}\\,\\beta\\log n
--   $$
--   and the shifted density floor
--   $$
--   m \\ge \\lambda\\,\\mu_0^{4/3}\\,n\\,r^{4/3}\\,(\\beta+2)\\log n.
--   $$
--   The shifted hypothesis is used to apply the pointwise theorem with parameter `beta+2`, giving per-coordinate failure `n^{-(beta+2)}` before the `n_1 n_2 <= n^2` union bound. Because the mean pointwise scale contains `sqrt(beta log n)`, this bridge also absorbs `sqrt((beta+2) log n) <= sqrt(2) sqrt(beta log n)` for `beta > 2` by enlarging the universal pointwise constant.
--
--   Under these hypotheses, there exist positive constants `Ccoef` and `ccoef`, depending only on the supplied base-bound constants, such that
--   $$
--   \\mathbb P_p\\{\\forall w_1, |H_{w_1}(\\Omega)| \\le C_{\\rm coef}\sqrt{\\beta\\log n}(\\mu_0 n r/m)^{3/2}\\}
--   \\ge 1-c_{\\rm coef}n^{-\\beta}.
--   $$
--   In Lean this is the event `QuadraticMiddleIndexDistinctMeanCoefficientBound Omega S p (...)`. This node records the explicit `beta+2` density requirement and should not be cited as eliminating that requirement.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. Exact Matrix Completion via Convex Optimization. arXiv:0805.4471 / Foundations of Computational Mathematics 9 (2009), 717--772. Exact locations: Section 6.3, Lemma 4.6 proof, PDF p. 30 equation (6.20), PDF pp. 32--33 third-term estimate; Section 6.2, PDF p. 29 after equation (6.17). PDF: https://pages.cs.wisc.edu/~brecht/papers/08.Candes.Recht.MatrixCompletion.pdf

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_middle_index_distinct_mean_coefficients_from_kernel_square_base_bounds_min_dim_shifted
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
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
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              ((β + 2) * Real.log (↑(max n₁ n₂))) →
        (∀ w1 : Fin n₁ × Fin n₂,
          ∀ Omega : Finset (Fin n₁ × Fin n₂),
          quadraticMiddleIndexDistinctMeanCoefficient Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1))) →
        (∀ w1 : Fin n₁ × Fin n₂,
          entrySupNorm
              (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
            Centry * μ₀ ^ 2 *
              (((r : ℝ) / (↑(min n₁ n₂))) ^ 2)) →
        (∀ w1 : Fin n₁ × Fin n₂,
          frobeniusNorm
              (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
            Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
              Real.rpow ((r : ℝ) / (↑(min n₁ n₂))) ((3 : ℝ) / 2)) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              QuadraticMiddleIndexDistinctMeanCoefficientBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef *
                  Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
                    Real.rpow
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                      ((3 : ℝ) / 2))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
