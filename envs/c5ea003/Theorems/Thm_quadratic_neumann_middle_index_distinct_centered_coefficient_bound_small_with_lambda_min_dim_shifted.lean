-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_centered_coefficient_bound_small_with_lambda_min_dim_shifted
-- name    : quadratic_neumann_middle_index_distinct_centered_coefficient_bound_small_with_lambda_min_dim_shifted
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-24T19:23:41.306514+00:00
-- url     : https://prove2.me/theorems/1e185fb1-39e3-440d-a37b-ec4c0aa4010e
-- statement:
--   This is a formal Lean wrapper, not a theorem stated verbatim in Candes--Recht. It is the source-backed strengthened replacement route for the middle-index-distinct centered quadratic coefficient bound: it combines the proved centered coefficient identity `quadratic_neumann_middle_index_distinct_centered_coefficient_entry_as_signed_scalar_fluctuation`, the corrected min-dimension kernel-square base bounds `quadratic_neumann_middle_index_distinct_kernel_square_base_entry_sup_norm_bound_min_dim` and `quadratic_neumann_middle_index_distinct_kernel_square_base_frobenius_norm_bound_min_dim`, and the proved shifted bridge `quadratic_neumann_middle_index_distinct_centered_coefficients_from_kernel_square_base_bounds_min_dim_shifted`.
--
--   Source locations: Candes--Recht, *Exact matrix completion via convex optimization*, Section 6.3 proof of Lemma 4.6, PDF p. 30 equation (6.20) for the cubic Neumann partition and PDF pp. 32--33 for the `omega_1 = omega_3 != omega_2` middle-index-distinct term; the kernel-square base estimates use Section 6, PDF p. 32 equations (6.1)--(6.2), with the tangent-kernel identities from Section 4.2, equations (4.7)--(4.8); the shifted coordinate-union pattern follows Section 6.2, PDF p. 29 after equation (6.17).
--
--   Let `M` be an `n_1 x n_2` rank-`r` matrix with SVD data `S`, let `n = max(n_1,n_2)`, and let `p = m/(n_1 n_2)`. The Bernoulli model samples each coordinate independently with probability `p`, and `bernoulliEventProb(p,E)` is the resulting probability. The incoherence hypotheses are `A0(S, mu_0)` and `A1(S, mu_1)`, where `mu_0` controls tangent-space coordinate spread and `mu_1` controls the sign-matrix entry scale. The parameter `beta > 2` controls failure rate `n^{-beta}`, and `lambda >= 1` is the sampling slack.
--
--   The statement deliberately assumes both sample floors
--   $$
--   m \ge \lambda\mu_0^{4/3} n r^{4/3}\,\beta\log n
--   $$
--   and
--   $$
--   m \ge \lambda\mu_0^{4/3} n r^{4/3}\, (\beta+2)\log n.
--   $$
--   The second floor is not cosmetic: the route applies the pointwise tail at exponent `beta+2`, then pays the `n_1 n_2 <= n^2` coordinate-union loss to recover a uniform event with failure `O(n^{-beta})`.
--
--   The conclusion is that there are positive constants `Ccoef, ccoef` such that
--   $$
--   \mathbb P_p\{\|Q_{1=3\ne2}^{\mathrm{centered}}(\Omega_2)\|_\infty
--   \le C_{\rm coef}\lambda^{-1}\}
--   \ge 1-c_{\rm coef} n^{-\beta},
--   $$
--   where the Lean event is `QuadraticMiddleIndexDistinctCenteredCoefficientBound Omega2 S p (Ccoef * Real.rpow lam (-1))`. This node should not be used to prove the older `beta`-only parent unless an independent argument supplies the strengthened `(beta+2)` sample floor.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. Exact Matrix Completion via Convex Optimization. arXiv:0805.4471 / Foundations of Computational Mathematics 9 (2009), 717--772. Exact locations: Section 6.3, Lemma 4.6 proof, PDF p. 30 equation (6.20), PDF pp. 32--33 middle-index-distinct term; Section 6, PDF p. 32 equations (6.1)--(6.2); Section 4.2 equations (4.7)--(4.8); Section 6.2, PDF p. 29 after equation (6.17). PDF: https://pages.cs.wisc.edu/~brecht/papers/08.Candes.Recht.MatrixCompletion.pdf

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_middle_index_distinct_centered_coefficient_bound_small_with_lambda_min_dim_shifted :
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
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              QuadraticMiddleIndexDistinctCenteredCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * Real.rpow lam (-1))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
