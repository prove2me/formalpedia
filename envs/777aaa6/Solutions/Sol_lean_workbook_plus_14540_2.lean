-- Prove2me | solution 2 for lean_workbook_plus_14540
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:42.717802+00:00
-- url     : https://prove2.me/submissions/8f1e1885-1601-4cd8-a78e-7a83bc60b42c

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) : |y| - |x| ≤ |x - y| := by
  rw [abs_sub_comm]
  exact abs_sub_abs_le_abs_sub y x
