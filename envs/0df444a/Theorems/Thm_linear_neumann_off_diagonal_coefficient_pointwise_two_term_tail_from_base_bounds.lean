-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_coefficient_pointwise_two_term_tail_from_base_bounds
-- name    : linear_neumann_off_diagonal_coefficient_pointwise_two_term_tail_from_base_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T15:51:46.795479+00:00
-- url     : https://prove2.me/theorems/fa2dbe5f-4a5a-4ba9-980d-12212807e7e3
-- statement:
--   This is the source-faithful fixed-coordinate Bernstein estimate for one entry of the off-diagonal first Neumann coefficient matrix in Candes--Recht Lemma 6.6.
--
--   Fix $w=(a,b)$ and write the coefficient entry $Q_{\Omega_2}(E)_w$ from equation (6.14) as the centered scalar sampling fluctuation of a base matrix $B^{(w)}$.  If
--   $$\|B^{(w)}\|_\infty\le A,\qquad \|B^{(w)}\|_F\le F,$$
--   then scalar Bernstein gives the two-term threshold
--   $$
--   |Q_{\Omega_2}(E)_w|\le C\left(\sqrt{\frac{(\beta+2)\log n}{p}}\,F
--   +\frac{(\beta+2)\log n}{p}\,A\right),\qquad p=\frac{m}{n_1n_2},
--   $$
--   with failure probability at most $c n^{-(\beta+2)}$.
--
--   In the formal statement, $A$ and $F$ are the Candes--Recht base-matrix scales
--   $$
--   A=C_{\rm entry}\mu_1\sqrt{\frac r{n_1n_2}}\frac{\mu_0r}{n},\qquad
--   F=C_{\rm fro}\mu_1\sqrt{\frac r{n_1n_2}}\sqrt{\frac{\mu_0r}{n}},\quad n=\max(n_1,n_2).
--   $$
--   The exponent $\beta+2$ is kept for the downstream coordinate union bound. Source location: Candes--Recht, Section 6.2, Lemma 6.6, equations (6.15)--(6.17).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_linear_neumann_offdiag_bernstein
open MatrixCompletion

theorem linear_neumann_off_diagonal_coefficient_pointwise_two_term_tail_from_base_bounds
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
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ w : Fin n₁ × Fin n₂,
        (∀ Omega2 : Finset (Fin n₁ × Fin n₂),
          linearNeumannOffDiagonalCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w.1 w.2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega2
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (linearNeumannOffDiagonalCoefficientBaseMatrix S w))) →
        entrySupNorm
            (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
          Centry * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (μ₀ * (r : ℝ) / (↑(max n₁ n₂))) →
        frobeniusNorm
            (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
          Cfro * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt (μ₀ * (r : ℝ) / (↑(max n₁ n₂))) →
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
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2)) := by
  sorry
