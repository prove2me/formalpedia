-- Prove2me | solution 1 for lean_workbook_plus_78929
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:00:23.769677+00:00
-- url     : https://prove2.me/submissions/86c1fa21-1bee-44b3-b869-e639bfe80feb

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (a : ℝ) : ∀ x, (x + a) = x + a := by
  norm_num
