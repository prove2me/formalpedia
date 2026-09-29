-- Prove2me | Theorems.Thm_linear_neumann_diagonal_contribution_under_general_sample_bound
-- name    : linear_neumann_diagonal_contribution_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T15:40:14.664649+00:00
-- url     : https://prove2.me/theorems/b535cf7d-37c1-4dac-bd45-0c00f67dd48b
-- statement:
--   Full diagonal contribution estimate for the first Neumann correction in the Theorem 1.3 sample regime.
--
--   Context and notation.  Equation (6.9) writes the diagonal part of $p^{-1}(P_\Omega-pI)H(E)$ as a centered random term plus a deterministic mean term.  The present theorem combines those two pieces.
--
--   Claim.  For $n=\max(n_1,n_2)$, if
--   $$
--   m\ge C'\max\{\mu_1^2,\sqrt{\mu_0}\mu_1,\mu_0 n^{1/4}\}\,nr\,\beta\log n
--   $$
--   with $C'$ sufficiently large and $\beta>2$, then
--   $$
--   \mathbb P_p\{\|S_0\|\le 1/16\}\ge 1-c n^{-\beta}.
--   $$
--
--   Here $S_0$ is the diagonal contribution from equation (6.8), and $p=m/(n_1n_2)$.
--
--   Source: Candès--Recht 2008, PDF p. 6, equation (1.9); PDF p. 26, equations (6.8)--(6.9); PDF p. 27, Theorem 6.3 applied to the centered term and Lemma 6.4 for the deterministic mean term.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_diagonal_contribution_under_general_sample_bound :
    ∃ Cdiag cdiag : ℝ, 0 < Cdiag ∧ 0 < cdiag ∧
      ∀ C' : ℝ, Cdiag ≤ C' →
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
                (linearNeumannDiagonalContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (1 : ℝ) / 16) ≥
          1 - cdiag * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
