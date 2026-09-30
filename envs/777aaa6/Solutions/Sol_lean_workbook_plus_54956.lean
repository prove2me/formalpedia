-- Prove2me | solution 1 for lean_workbook_plus_54956
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:53:20.106295+00:00
-- url     : https://prove2.me/submissions/34c8ab13-5f37-41b1-adce-02ba043e1ed0

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (a b : ℝ) : (a - b) ^ 4 ≥ 0 := by
  positivity
