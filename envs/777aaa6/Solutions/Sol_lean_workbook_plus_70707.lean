-- Prove2me | solution 1 for lean_workbook_plus_70707
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:00:06.927611+00:00
-- url     : https://prove2.me/submissions/e2181312-b0cf-4798-94a3-bdcb2a8b0356

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ x : ℝ, Real.sqrt ((x-1)^2) = x-1) := by
  intro h
  have h0 := h 0
  norm_num at h0

#print axioms solution
