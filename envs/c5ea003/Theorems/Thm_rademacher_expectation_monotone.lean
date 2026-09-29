-- Prove2me | Theorems.Thm_rademacher_expectation_monotone
-- name    : rademacher_expectation_monotone
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T04:49:58.927971+00:00
-- url     : https://prove2.me/theorems/362b79ff-e4a5-4dcf-aff0-0fe2f1104b8e
-- statement:
--   Monotonicity of the Rademacher expectation. If for every Rademacher sign realization $S$ (encoded as the finite set of coordinates carrying a $+1$ sign) we have $F(S)\le G(S)$, then the Rademacher expectations satisfy `rademacherExpectation F` $\le$ `rademacherExpectation G`. The expectation is a finite sum of values weighted by nonnegative uniform Rademacher weights.
-- source:
--   Candes & Recht, Exact matrix completion via convex optimization, CACM 55.6 (2012).

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion

theorem rademacher_expectation_monotone :
    ∀ {n₁ n₂ : ℕ}
      (F G : Finset (Fin n₁ × Fin n₂) → ℝ),
      (∀ S, F S ≤ G S) →
      rademacherExpectation F ≤ rademacherExpectation G := by sorry
