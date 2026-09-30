-- Prove2me | solution 1 for lean_workbook_plus_74145
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:49:55.905799+00:00
-- url     : https://prove2.me/submissions/e2c27126-53d2-4f8e-855e-6cf276f384db

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∀ n : ℤ, 100 ∣ 100 * n := by
  norm_num
