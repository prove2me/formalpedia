-- Prove2me | solution 1 for lean_workbook_plus_36894
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:59:18.138502+00:00
-- url     : https://prove2.me/submissions/88cef163-7825-4c71-9aaf-a7f4be9a5dae

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) : x / (1 + x ^ 2) ≤ 1 / 2 ∧ (x = 1 ↔ x / (1 + x ^ 2) = 1 / 2) := by
  have hd : 0 < 1+x^2 := by positivity
  constructor
  · apply (div_le_iff₀ hd).2
    nlinarith [sq_nonneg (x-1)]
  · constructor
    · rintro rfl; norm_num
    · intro h
      have hh := (div_eq_iff (ne_of_gt hd)).1 h
      nlinarith
