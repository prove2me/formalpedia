-- Prove2me | solution 1 for lean_workbook_plus_25287
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:49.088678+00:00
-- url     : https://prove2.me/submissions/9024e6d5-3efe-47c4-a502-6e840dd466b5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : (a - b) ^ 4 + (a - c) ^ 4 + (a - d) ^ 4 + (b - c) ^ 4 + (b - d) ^ 4 + (c - d) ^ 4 ≥ 0 := by
  (intros; positivity)
