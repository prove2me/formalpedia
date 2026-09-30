-- Prove2me | solution 1 for lean_workbook_plus_28437
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:42:38.982781+00:00
-- url     : https://prove2.me/submissions/08051e9d-a9f0-40ef-a2c5-18a195cdf206

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (1024:ℝ)^56 < 5 * 10^168 := by
  norm_num
