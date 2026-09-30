-- Prove2me | solution 1 for lean_workbook_plus_45835
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:12:33.737781+00:00
-- url     : https://prove2.me/submissions/20997ad3-7ca0-41a0-8d0c-14fb360fe461

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (a b : ℂ) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
  norm_num
