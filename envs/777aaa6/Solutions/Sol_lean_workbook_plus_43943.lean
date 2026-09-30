-- Prove2me | solution 1 for lean_workbook_plus_43943
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:49:15.449357+00:00
-- url     : https://prove2.me/submissions/7cbc061e-eec2-4611-8109-ab9a802ee50b

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (z : ℂ) : ‖z‖^2 = ‖z^2‖ := by
  norm_num
