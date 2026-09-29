-- Prove2me | solution 1 for lean_workbook_plus_33494
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:06:49.030239+00:00
-- url     : https://prove2.me/submissions/94718368-8541-4a01-8661-d09240a9590c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (m : ℝ) (hm : 2 * m + 3 ≤ m + 8) (hn : m + 8 ≤ 4 * m - 13) : - 13 / 8 ≤ m ∧ m ≤ 3 / 2 := by
  (intros; linarith)
