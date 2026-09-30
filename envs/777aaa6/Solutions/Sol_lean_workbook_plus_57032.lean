-- Prove2me | solution 1 for lean_workbook_plus_57032
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:57:32.584844+00:00
-- url     : https://prove2.me/submissions/2b2d800a-3220-493a-a592-111394664d7f

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (n : ℕ) (hn : 0 < n) : n = n := by
  norm_num
