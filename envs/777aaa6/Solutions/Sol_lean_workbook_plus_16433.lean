-- Prove2me | solution 1 for lean_workbook_plus_16433
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:15.933705+00:00
-- url     : https://prove2.me/submissions/a3d4667d-dc2f-4352-880b-503637708528

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (h₁ : (2:ℝ)/3 < x) (h₂ : x < 1) : (1 - x) / (1 + 3 * x) < 1 / 3 := by
  (intros; field_simp; nlinarith [sq_nonneg (x)])
