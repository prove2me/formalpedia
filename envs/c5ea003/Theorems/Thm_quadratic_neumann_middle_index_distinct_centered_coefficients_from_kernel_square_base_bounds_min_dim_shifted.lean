-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_centered_coefficients_from_kernel_square_base_bounds_min_dim_shifted
-- name    : quadratic_neumann_middle_index_distinct_centered_coefficients_from_kernel_square_base_bounds_min_dim_shifted
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-24T19:11:08.28342+00:00
-- url     : https://prove2.me/theorems/01b212b5-e585-419f-a9fd-fd38efaacfb9
-- statement:
--   This is a formal Lean bridge, not a theorem stated verbatim in Candes--Recht. It connects the source-backed pointwise centered-tail theorem `quadratic_neumann_middle_index_distinct_centered_coefficient_pointwise_tail_from_kernel_square_base_bounds_min_dim` with the source-backed shifted union-bound theorem `quadratic_neumann_middle_index_distinct_centered_coefficients_uniform_from_shifted_pointwise_tails` for the middle-index-distinct quadratic Neumann term. Source location: Candes--Recht, *Exact matrix completion via convex optimization*, Section 6.3, proof of Lemma 4.6, PDF p. 30 equation (6.20) for the partition of the cubic Neumann sum, and PDF pp. 32--33 for the third term `omega_1 = omega_3 != omega_2`; the scalar Bernstein and coordinate-union pattern follows the same Section 6.2 mechanism, PDF p. 29 after equation (6.17).
--
--   Let `M` be an `n_1 x n_2` rank-`r` matrix with SVD data `S` satisfying the incoherence hypotheses `A0(S, mu_0)` and `A1(S, mu_1)`. Here `mu_0` controls the singular-vector coherence, `mu_1` controls the entry size of the sign matrix, `n = max(n_1,n_2)`, and `p = m/(n_1 n_2)`. In the Bernoulli model, `Omega_2` includes each coordinate independently with probability `p`, and `bernoulliEventProb(p, E)` is the probability of event `E` under this product model. The parameter `beta > 2` controls the polynomial failure rate `n^{-beta}`, and `lambda >= 1` is the density slack parameter.
--
--   Assume the centered coefficient identity for every coordinate `w_1`, and assume the corrected min-dimension kernel-square base bounds
--   $$
--   \\|B_{w_1}\\|_\\infty \\le C_{\\rm entry}\\mu_0^2 (r/\\min(n_1,n_2))^2,
--   $$
--   and
--   $$
--   \\|B_{w_1}\\|_F \\le C_{\\rm fro}\\mu_0^{3/2} (r/\\min(n_1,n_2))^{3/2}.
--   $$
--   This bridge deliberately requires both the usual density floor
--   $$
--   m \\ge \\lambda\\,\\mu_0^{4/3}\\,n\\,r^{4/3}\\,\\beta\\log n
--   $$
--   and the strengthened shifted density floor
--   $$
--   m \\ge \\lambda\\,\\mu_0^{4/3}\\,n\\,r^{4/3}\\,(\\beta+2)\\log n.
--   $$
--   The strengthened `beta+2` hypothesis is essential for this formal route: the pointwise tail is applied with parameter `beta+2`, producing per-coordinate failure of order `n^{-(beta+2)}`, and the shifted uniformization theorem then pays the `n_1 n_2 <= n^2` union-bound loss to obtain a uniform `n^{-beta}` bound.
--
--   Under these hypotheses, there exist positive universal constants `Ccoef` and `ccoef`, depending only on the supplied base-bound constants, such that
--   $$
--   \\mathbb P_p\\{\\|Q(\\Omega_2)\\|_\\infty \\le C_{\\rm coef}\\lambda^{-1}\\}\\ge 1-c_{\\rm coef}n^{-\\beta},
--   $$
--   where `Q(Omega_2)` is the centered conditional coefficient matrix `quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S p`, and the Lean event is `QuadraticMiddleIndexDistinctCenteredCoefficientBound Omega2 S p (Ccoef * lambda^{-1})`. This node should not be cited as removing the `beta+2` sample-density requirement; it is exactly the formal bridge that records that strengthened hypothesis.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. Exact Matrix Completion via Convex Optimization. arXiv:0805.4471 / Foundations of Computational Mathematics 9 (2009), 717--772. Exact locations: Section 6.3, Lemma 4.6 proof, PDF p. 30 equation (6.20), PDF pp. 32--33 third-term estimate; Section 6.2, PDF p. 29 after equation (6.17). PDF: https://pages.cs.wisc.edu/~brecht/papers/08.Candes.Recht.MatrixCompletion.pdf

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_middle_index_distinct_centered_coefficients_from_kernel_square_base_bounds_min_dim_shifted
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
          ∀ Omega2 : Finset (Fin n₁ × Fin n₂),
          quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1.1 w1.2 =
            signMatrix S w1.1 w1.2 *
              matrixEntrySum
                (centeredSamplingFluctuation Omega2
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
            (fun Omega2 =>
              QuadraticMiddleIndexDistinctCenteredCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * Real.rpow lam (-1))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
