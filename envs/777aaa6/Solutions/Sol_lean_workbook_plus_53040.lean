-- Prove2me | solution 1 for lean_workbook_plus_53040
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:47:06.87268+00:00
-- url     : https://prove2.me/submissions/60a1aa43-d3f9-4374-ad7a-7b85d2e2179f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {x : ℝ} (hx : 0 < x ∧ x < 1) : (3 * x ^ 2 - 1) ^ 2 * (5 * x ^ 2 - 1) ^ 2 ≥ 0 := by
  (intros; positivity)
