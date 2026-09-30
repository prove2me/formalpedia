-- Prove2me | solution 1 for lean_workbook_plus_81507
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:28:27.457854+00:00
-- url     : https://prove2.me/submissions/fae27c40-e6ba-496a-839e-40c3bb2773db

import Mathlib

theorem solution : ∀ p : ℝ,
    12 * p - p ^ 3 ≥ 27 * p - (p ^ 2 + 3) * (p + 3) ↔
      3 * (p - 1) * (p - 3) ≥ 0 := by
  intro p
  constructor <;> intro h <;> nlinarith
