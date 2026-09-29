-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_contribution_under_general_sample_bound
-- name    : linear_neumann_off_diagonal_contribution_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T15:41:54.432085+00:00
-- url     : https://prove2.me/theorems/b29300ea-af73-4420-922e-cdd7f602930f
-- statement:
--   Off-diagonal contribution estimate for the first Neumann correction in the full Theorem 1.3 sample regime.
--
--   Context and notation.  After the diagonal/off-diagonal split in equation (6.8), the off-diagonal term is decoupled in Lemma 6.5.  The decoupled term is written in equations (6.13)--(6.14) using the conditional coefficient matrix $Q(E)$, and Lemma 6.6 bounds $\|Q(E)\|_\infty$ by Bernstein's inequality and a coordinate union bound.
--
--   Claim.  For $n=\max(n_1,n_2)$, under the full Theorem 1.3 sample lower bound
--   $$
--   m\ge C'\max\{\mu_1^2,\sqrt{\mu_0}\mu_1,\mu_0 n^{1/4}\}\,nr\,\beta\log n,
--   $$
--   with $C'$ sufficiently large and $\beta>2$, the original off-diagonal contribution satisfies
--   $$
--   \mathbb P_p\{\|S_1\|\le 1/16\}\ge 1-c n^{-\beta}.
--   $$
--
--   Proof role.  This theorem uses the already repaired general-sample Lemma 6.6 coefficient estimate, then applies Theorem 6.3 conditionally to the outer sample and transfers the decoupled estimate back to the original Bernoulli model.
--
--   Source: Candès--Recht 2008, PDF p. 6, equation (1.9); PDF pp. 27--29, equations (6.12)--(6.18).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_off_diagonal_contribution_under_general_sample_bound :
    ∃ Coff coff : ℝ, 0 < Coff ∧ 0 < coff ∧
      ∀ C' : ℝ, Coff ≤ C' →
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
                (linearNeumannOffDiagonalContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (1 : ℝ) / 16) ≥
          1 - coff * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
