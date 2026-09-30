-- Prove2me | solution 1 for lean_workbook_plus_11333
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:03.806546+00:00
-- url     : https://prove2.me/submissions/350e7307-86fd-4e92-8a07-deff64c7a27c

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (n : ℕ) : n = n := by
  norm_num
