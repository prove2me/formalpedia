-- Prove2me | Theorems.Thm_linear_neumann_diagonal_mean_contribution_under_general_sample_bound
-- name    : linear_neumann_diagonal_mean_contribution_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T15:38:49.10054+00:00
-- url     : https://prove2.me/theorems/73755202-836a-48ab-90dc-f5a2fd3a7c9b
-- statement:
--   Deterministic mean-diagonal estimate in the full Theorem 1.3 sample regime.
--
--   Context and notation.  In equation (6.9), Candès--Recht split the diagonal part $S_0$ into a centered random term and a deterministic mean term.  The mean term is
--   $$
--   (1-p)\sum_{i,j}H_{ij}e_i e_j^\top,
--   $$
--   where $H_{ij}=p^{-1}E_{ij}\langle P_T(e_i e_j^\top),e_i e_j^\top\rangle$.
--
--   Claim.  Under the same full Theorem 1.3 sample lower bound
--   $$
--   m\ge C'\max\{\mu_1^2,\sqrt{\mu_0}\mu_1,\mu_0 n^{1/4}\}\,nr\,\beta\log n,
--   $$
--   with $C'$ sufficiently large, the deterministic mean diagonal contribution has spectral norm at most $1/32$.
--
--   Proof role.  This is a formal bridge from the already proved lambda-form mean estimate to the theorem-regime statement, choosing a fixed large internal lambda.  No new probabilistic theorem is used here.
--
--   Source: Candès--Recht 2008, PDF p. 6, equation (1.9); PDF p. 26, equation (6.9); PDF p. 27, Lemma 6.4/equations (6.10)--(6.11).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_diagonal_mean_contribution_under_general_sample_bound :
    ∃ Cmean : ℝ, 0 < Cmean ∧
      ∀ C' : ℝ, Cmean ≤ C' →
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
        spectralNorm
            (linearNeumannDiagonalMeanContribution S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          (1 : ℝ) / 32 := by
  sorry
