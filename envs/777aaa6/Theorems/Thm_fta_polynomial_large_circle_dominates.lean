-- Prove2me | Theorems.Thm_fta_polynomial_large_circle_dominates
-- name    : fta_polynomial_large_circle_dominates
-- status  : Proved
-- author  : @Henry Yuen
-- created : 2026-05-22T14:59:36.557622+00:00
-- url     : https://prove2.me/theorems/5ed3d5bf-2205-41a2-9116-e4fe4d626408
-- statement:
--   Large-radius leading-term domination for complex polynomials on a boundary circle.
-- source:
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Polynomial/Basic.html#Complex.exists_root

import Definitions.Def_fta_winding_infra

theorem fta_polynomial_large_circle_dominates (f : Polynomial ℂ) (hf : 0 < f.degree) :
    ∃ R : ℝ, 0 < R ∧ FtaLeadingDominatesOnBoundary f R := by
  sorry
