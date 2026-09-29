-- Prove2me | solution 1 for lean_workbook_plus_30141
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:28.085394+00:00
-- url     : https://prove2.me/submissions/44c17c7e-47fe-4b36-9d82-e519472ff448

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, 0 < x ∧ x < 1 → ∃ y, ∑' i : ℕ, (1/2)^i = y := by
  norm_num
