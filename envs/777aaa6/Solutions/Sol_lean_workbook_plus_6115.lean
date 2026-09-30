-- Prove2me | solution 1 for lean_workbook_plus_6115
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:03:34.512576+00:00
-- url     : https://prove2.me/submissions/98a32469-95d3-418a-9a6c-fad2f33947c4

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (n r : ℕ) : ∃ k, k = n.choose r := by
  norm_num
