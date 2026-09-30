-- Prove2me | solution 1 for lean_workbook_plus_52119
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:47:21.88427+00:00
-- url     : https://prove2.me/submissions/6a9b05b8-1333-4d48-9231-7e6f128ea6f1

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (n : ℕ) : Odd (2 * n + 1) := by
  norm_num
