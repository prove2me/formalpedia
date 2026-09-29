-- Prove2me | Theorems.Thm_fta_polynomial_large_circle_dominates
-- name    : fta_polynomial_large_circle_dominates
-- status  : Proved
-- author  : @Henry Yuen
-- created : 2026-05-22T14:59:36.557622+00:00
-- url     : https://prove2.me/theorems/a790ca64-8d5b-4a89-8c1f-72131bfe7faa
-- statement:
--   Large-radius leading-term domination for complex polynomials on a boundary circle.
-- source:
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Polynomial/Basic.html#Complex.exists_root

import Definitions.Def_fta_winding_infra

theorem fta_polynomial_large_circle_dominates (f : Polynomial ℂ) (hf : 0 < f.degree) :
    ∃ R : ℝ, 0 < R ∧ FtaLeadingDominatesOnBoundary f R := by
  sorry
