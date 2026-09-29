-- Prove2me | solution 1 for lean_workbook_plus_53016
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:03:38.837168+00:00
-- url     : https://prove2.me/submissions/00ec9bdd-fdff-4d3f-8501-edbb7f86aa0f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ q : ℝ, (q^2 * (1 + q)^2 * (1 - 3*q)^2) ≥ 0 := by
  (intros; positivity)
