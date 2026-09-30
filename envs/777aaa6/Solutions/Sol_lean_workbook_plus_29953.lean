-- Prove2me | solution 1 for lean_workbook_plus_29953
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:42:38.384786+00:00
-- url     : https://prove2.me/submissions/50d7fb0f-9a40-4b65-bfe6-8254d00f3f89

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (u : ℝ) : (u - 1) ^ 2 ≥ 0 := by
  positivity
