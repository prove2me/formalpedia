-- Prove2me | Theorems.Thm_linear_neumann_diagonal_centered_contribution_under_general_sample_bound
-- name    : linear_neumann_diagonal_centered_contribution_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T15:37:09.586426+00:00
-- url     : https://prove2.me/theorems/8da1e4d4-4dfe-4cfb-b866-88dad1c26c47
-- statement:
--   Centered diagonal estimate for the first Neumann correction in the full Theorem 1.3 sample regime.
--
--   Context and notation.  Let $p=m/(n_1n_2)$ and let $S$ be the SVD data of the rank-$r$ matrix $M$.  The diagonal contribution $S_0$ in equation (6.8) is decomposed in equation (6.9).  This theorem controls only the random centered part
--   $$
--   p^{-1}(1-2p)(P_\Omega-pI)H
--   $$
--   where $H$ is the fixed diagonal base matrix from equation (6.9).
--
--   Claim.  There are universal constants $C,c>0$ such that, whenever
--   $$
--   m\ge C'\max\{\mu_1^2,\sqrt{\mu_0}\mu_1,\mu_0 n^{1/4}\}\,nr\,\beta\log n,\qquad C'\ge C,\quad \beta>2,
--   $$
--   the Bernoulli probability of
--   $$
--   \left\|S_{0,\mathrm{centered}}\right\|\le {1\over 32}
--   $$
--   is at least $1-c n^{-\beta}$, with $n=\max(n_1,n_2)$.
--
--   Proof role.  This is the source-correct replacement for the legacy lambda/max-denominator centered-diagonal route.  It uses the fixed-matrix Theorem 6.3, the exact equation (6.9) representation, and the proved rectangular-safe base-entry bound with denominator $\min(n_1,n_2)$.
--
--   Source: Candès--Recht 2008, PDF p. 6, equation (1.9); PDF p. 26, equation (6.9); PDF p. 27, the centered-diagonal display; and the rectangular convention immediately before Section 6.1.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_diagonal_centered_contribution_under_general_sample_bound :
    ∃ Ccenter ccenter : ℝ, 0 < Ccenter ∧ 0 < ccenter ∧
      ∀ C' : ℝ, Ccenter ≤ C' →
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
            (fun Omega =>
              spectralNorm
                (linearNeumannDiagonalCenteredContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (1 : ℝ) / 32) ≥
          1 - ccenter * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
