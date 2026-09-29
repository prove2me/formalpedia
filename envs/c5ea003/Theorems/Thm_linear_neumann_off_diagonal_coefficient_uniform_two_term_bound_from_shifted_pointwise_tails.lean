-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_coefficient_uniform_two_term_bound_from_shifted_pointwise_tails
-- name    : linear_neumann_off_diagonal_coefficient_uniform_two_term_bound_from_shifted_pointwise_tails
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T16:08:12.24464+00:00
-- url     : https://prove2.me/theorems/0c0957be-f15c-4c53-a97b-f6213982c9fd
-- statement:
--   This theorem is the finite-coordinate union bound for the raw two-term Bernstein estimate in Candes--Recht Lemma 6.6.
--
--   Let $n=\max(n_1,n_2)$ and $p=m/(n_1n_2)$.  Suppose that for every coordinate $w=(a,b)$ of the coefficient matrix $Q_{\Omega_2}(E)$, the pointwise event
--   $$
--   |Q_{\Omega_2}(E)_w|\le C_{\rm point}\left(
--   \sqrt{\frac{(\beta+2)\log n}{p}}\,F
--   +\frac{(\beta+2)\log n}{p}\,A\right)
--   $$
--   has probability at least $1-c_{\rm point}n^{-(\beta+2)}$, where
--   $$
--   A=C_{\rm entry}\mu_1\sqrt{\frac r{n_1n_2}}\frac{\mu_0r}{n},\qquad
--   F=C_{\rm fro}\mu_1\sqrt{\frac r{n_1n_2}}\sqrt{\frac{\mu_0r}{n}}.
--   $$
--   Then, after union bounding over $n_1n_2\le n^2$ entries, the uniform coefficient event
--   $$
--   \|Q_{\Omega_2}(E)\|_\infty\le C\left(
--   \sqrt{\frac{(\beta+2)\log n}{p}}\,F
--   +\frac{(\beta+2)\log n}{p}\,A\right)
--   $$
--   holds with probability at least $1-cn^{-\beta}$.
--
--   Source location: Candes--Recht, Section 6.2, Lemma 6.6, equations (6.15)--(6.17), and the union bound immediately after equation (6.17).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_linear_neumann_offdiag_bernstein
open MatrixCompletion

theorem linear_neumann_off_diagonal_coefficient_uniform_two_term_bound_from_shifted_pointwise_tails
    (Cpoint cpoint Centry Cfro : ℝ) :
    0 < Cpoint → 0 < cpoint →
    ∃ Ctwo ctwo : ℝ, 0 < Ctwo ∧ 0 < ctwo ∧
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
                  Cpoint *
                    (Real.sqrt
                        (((β + 2) * Real.log (↑(max n₁ n₂))) /
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (Cfro * μ₁ *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                          Real.sqrt (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))) +
                      (((β + 2) * Real.log (↑(max n₁ n₂))) /
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                        (Centry * μ₁ *
                          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                            (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))))) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              LinearNeumannOffDiagonalCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ctwo *
                  (Real.sqrt
                      (((β + 2) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    (Cfro * μ₁ *
                      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        Real.sqrt (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))) +
                    (((β + 2) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (Centry * μ₁ *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                          (μ₀ * (r : ℝ) / (↑(max n₁ n₂))))))) ≥
          1 - ctwo * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
