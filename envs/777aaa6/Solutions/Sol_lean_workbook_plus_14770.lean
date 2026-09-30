-- Prove2me | solution 1 for lean_workbook_plus_14770
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:03:39.430932+00:00
-- url     : https://prove2.me/submissions/e0af570b-293f-4397-9ae9-ad76541ade2e

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : √((-2 : ℝ) ^ 2) = |(-2 : ℝ)| := by
  simp
