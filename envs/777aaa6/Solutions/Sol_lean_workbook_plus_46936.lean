-- Prove2me | solution 1 for lean_workbook_plus_46936
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:57:35.682772+00:00
-- url     : https://prove2.me/submissions/504be75c-f81c-4a89-87dd-cb306d52f5a9

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 1 ∈ ({1, 2, 3} : Finset ℕ) := by
  norm_num
