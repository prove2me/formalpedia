-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_coefficient_bound_small_with_lambda
-- name    : linear_neumann_off_diagonal_coefficient_bound_small_with_lambda
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T00:56:01.586627+00:00
-- url     : https://prove2.me/theorems/2bbc0f94-a5e1-4b51-983e-a5964fc70695
-- statement:
--   This node is the Lemma 6.6 high-probability bound for the conditional coefficient matrix in the off-diagonal part of the first Neumann correction.
--
--   Let $p=m/(n_1n_2)$, $n=\max(n_1,n_2)$, and let $E=UV^{\mathsf T}$ be the sign matrix of the rank-$r$ matrix.  After the two-copy decoupling of the off-diagonal contribution in Candes--Recht equation (6.13), the random matrix is controlled through a coefficient matrix $Q_{\Omega_2}(E)$ defined entrywise by equation (6.14).
--   The theorem asserts that, under $A0(S,\mu_0)$, $A1(S,\mu_1)$, $\beta>2$, $\lambda\ge 1$, and
--   $$m\ge \lambda\,\mu_1\max\{\sqrt{\mu_0},\mu_1\}\,nr\,\beta\log n,$$
--   one has with probability at least $1-c n^{-\beta}$ the coefficient bound
--   $$\|Q_{\Omega_2}(E)\|_\infty
--   \le C\,\mu_1\sqrt{\frac r{n_1n_2}}
--   \sqrt{\frac{\mu_0 n r\,\beta\log n}{m}}.$$
--
--   Repair note. The legacy sketch for this node routed through a fixed-matrix spectral sampling estimate for the sign matrix.  The paper does not prove Lemma 6.6 that way; it identifies each entry as a scalar fluctuation, applies Bernstein to that scalar sum, and takes a coordinate union bound. Source location: Candes--Recht, Section 6.2, equations (6.13)--(6.17) and the union bound immediately after (6.17).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_off_diagonal_coefficient_bound_small_with_lambda :
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
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
  sorry
