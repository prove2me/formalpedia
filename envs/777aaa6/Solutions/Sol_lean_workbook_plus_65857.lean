-- Prove2me | solution 1 for lean_workbook_plus_65857
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:49:14.79421+00:00
-- url     : https://prove2.me/submissions/c6c2b180-1f52-4e7f-bd7f-2bb4766f941a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) / (9 * n + 7) < 1 / 9 := by
  (intros; field_simp; nlinarith [sq_nonneg (n)])
