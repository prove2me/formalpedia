-- Prove2me | solution 1 for lean_workbook_plus_27685
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:53.395453+00:00
-- url     : https://prove2.me/submissions/aa628e46-bd33-483e-9618-16500d88bf25

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (a : ℝ) : a^2 + 1 ≥ a := by
  nlinarith [sq_nonneg a]
