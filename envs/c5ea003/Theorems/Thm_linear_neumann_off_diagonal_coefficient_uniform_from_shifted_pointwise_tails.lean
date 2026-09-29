-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_coefficient_uniform_from_shifted_pointwise_tails
-- name    : linear_neumann_off_diagonal_coefficient_uniform_from_shifted_pointwise_tails
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T15:22:24.257652+00:00
-- url     : https://prove2.me/theorems/f641e47e-a872-429a-aee3-9e716756b6ee
-- statement:
--   This theorem is the corrected finite union-bound step in Candes--Recht Lemma 6.6 for the off-diagonal first Neumann coefficient matrix.
--
--   Let $p=m/(n_1n_2)$, $n=\max(n_1,n_2)$, and let $Q_{\Omega_2}(E)$ denote the coefficient matrix defined in equation (6.14) after decoupling the off-diagonal term in equation (6.13).  Suppose that for every coordinate $w=(a,b)$ we already know a pointwise scalar Bernstein tail
--   $$
--   \mathbb P\!\left(|Q_{\Omega_2}(E)_w|\le
--   C_{\rm point}\,\mu_1\sqrt{\frac r{n_1n_2}}
--   \sqrt{\frac{\mu_0nr\,\beta\log n}{m}}\right)
--   \ge 1-c_{\rm point}n^{-(\beta+2)}.
--   $$
--   Then, after increasing only universal constants, the simultaneous entrywise event satisfies
--   $$
--   \mathbb P\!\left(\|Q_{\Omega_2}(E)\|_\infty\le
--   C\,\mu_1\sqrt{\frac r{n_1n_2}}
--   \sqrt{\frac{\mu_0nr\,\beta\log n}{m}}\right)
--   \ge 1-cn^{-\beta}.
--   $$
--
--   The exponent shift from $\beta+2$ to $\beta$ exactly pays for the $n_1n_2\le n^2$ coordinate union bound. Source location: Candes--Recht, Section 6.2, Lemma 6.6, equations (6.15)--(6.17), and the union bound immediately after (6.17).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_linear_neumann_offdiag_bernstein
open MatrixCompletion

theorem linear_neumann_off_diagonal_coefficient_uniform_from_shifted_pointwise_tails
    (Cpoint cpoint : ℝ) :
    0 < Cpoint → 0 < cpoint →
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
        (∀ w : Fin n₁ × Fin n₂,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega2 =>
                |linearNeumannOffDiagonalCoefficientMatrix Omega2 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w.1 w.2| ≤
                  Cpoint * μ₁ *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      Real.sqrt
                        ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                            (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ))) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2))) →
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
