-- Prove2me | solution 1 for lean_workbook_plus_22241
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:00:24.587947+00:00
-- url     : https://prove2.me/submissions/33c3fd25-f5ed-4357-9f33-a036b202193a

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (n : ℚ) : n^2 = (n-1)*(n+1)+1 := by
  nlinarith
