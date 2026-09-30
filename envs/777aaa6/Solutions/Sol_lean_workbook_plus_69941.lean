-- Prove2me | solution 1 for lean_workbook_plus_69941
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:47:22.603978+00:00
-- url     : https://prove2.me/submissions/6b581fcf-b19f-4fe4-ba9d-244743e16860

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (n : ℕ) : n % 10 = n % 10 := by
  norm_num
