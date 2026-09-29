-- Prove2me | Theorems.Thm_general_sample_bound_implies_lemma66_density_bound
-- name    : general_sample_bound_implies_lemma66_density_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T10:38:39.524222+00:00
-- url     : https://prove2.me/theorems/fa1ca037-fe25-4e8d-9327-3eb39973cdd8
-- statement:
--   Formalizes a sourced Matrix Completion subproblem used in the Candes--Recht Theorem 1.3 decomposition. Source and mathematical role are documented in the Lean theorem docstring.
-- source:
--   Candes--Recht 2008, Exact Matrix Completion via Convex Optimization

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

/-- The global sample lower bound in Candes--Recht Theorem 1.3 implies the
sampling-density proviso used in Lemma 6.6.

In square notation Lemma 6.6 requires `n p >= const * mu0 * r * beta log n`.
For the rectangular formalization with `N = max n₁ n₂` and
`p = m / (n₁ n₂)`, the same proviso is equivalently recorded here as
`m >= const * mu0 * N * r * beta log N`.  This follows from the
`mu0 * N^(1/4)` branch of the global sample complexity.

Source: Candes--Recht 2008, PDF p. 6, Theorem 1.3/equation (1.9);
PDF p. 21, equation (4.19); and PDF p. 28, Lemma 6.6 immediately after
equation (6.15). -/

theorem general_sample_bound_implies_lemma66_density_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        (m : ℝ) ≥
          ((8 : ℝ) / 3) * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) := by
  sorry
