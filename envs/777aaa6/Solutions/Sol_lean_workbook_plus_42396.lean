-- Prove2me | solution 1 for lean_workbook_plus_42396
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:17:21.327065+00:00
-- url     : https://prove2.me/submissions/6ae6d9ee-f846-4474-a40d-563a4bba5c59

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (t : ℝ) (ht : 1 ≤ t) : (t + 2) / (t + 1) ≥ 5 / 6 + 2 / (3 * t) := by
  (intros; field_simp; nlinarith [sq_nonneg (t)])
