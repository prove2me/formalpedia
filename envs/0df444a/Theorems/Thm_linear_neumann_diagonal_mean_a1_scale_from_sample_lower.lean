-- Prove2me | Theorems.Thm_linear_neumann_diagonal_mean_a1_scale_from_sample_lower
-- name    : linear_neumann_diagonal_mean_a1_scale_from_sample_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-23T16:01:07.645055+00:00
-- url     : https://prove2.me/theorems/b57d2ebd-a59a-49e2-94b5-a0096f945faf
-- statement:
--   This is the scalar absorption step for the deterministic mean part of the diagonal first Neumann correction.
--
--   Set
--   $$
--   p={m\over n_1n_2},\qquad n=\max(n_1,n_2).
--   $$
--   The A1-effective Lemma 6.4 bound produces the deterministic scale
--   $$
--   C\,p^{-1}(1-p){\mu_1^2 r\over \min(n_1,n_2)}.
--   $$
--   Under the Lemma 4.5 sample lower bound
--   $$
--   m\ge \lambda\mu_1\max\{\sqrt{\mu_0},\mu_1\}\,nr\,\beta\log n,
--   $$
--   with $\beta>2$ and $\lambda\ge1$, this scale is bounded by a universal multiple of $\lambda^{-1}$.
--
--   Source: Candes-Recht 2008, PDF p. 20, Lemma 4.5, and PDF p. 27, the deterministic estimate following Lemma 6.4 in equation (6.9).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_diagonal_mean_a1_scale_from_sample_lower
    (Cdiag : ℝ) :
    0 < Cdiag →
    ∃ Cscale : ℝ, 0 < Cscale ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        Cdiag *
            ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
                (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) *
              (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂)))) ≤
          Cscale * Real.rpow lam (-1) := by
  sorry
