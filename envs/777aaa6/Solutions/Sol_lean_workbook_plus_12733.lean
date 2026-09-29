-- Prove2me | solution 1 for lean_workbook_plus_12733
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:32:08.949968+00:00
-- url     : https://prove2.me/submissions/a5bd2a5f-26a0-4937-8bb6-6b05f7f075db

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by
  (intros; positivity)
