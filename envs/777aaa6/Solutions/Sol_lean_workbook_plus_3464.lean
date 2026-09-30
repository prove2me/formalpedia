-- Prove2me | solution 1 for lean_workbook_plus_3464
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:12:30.364245+00:00
-- url     : https://prove2.me/submissions/a56931f4-5765-4bcb-9ea5-304ef15b0f64

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 10^30 < 2^100 ∧ 2^100 < 10^31 := by
  norm_num
