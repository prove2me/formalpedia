-- Prove2me | solution 1 for lean_workbook_plus_70087
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:00:05.914541+00:00
-- url     : https://prove2.me/submissions/1dd324f0-700e-48fd-9bc6-8625511fe035

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℝ,
    (a^2 + b^2 + c^2) / (a * b + b * c + c * a) +
    (8 * a * b * c) / (a + b) / (b + c) / (c + a) ≥ 2) := by
  intro h
  have h0 := h 0 0 0
  norm_num at h0
  exact (by norm_num : ¬ (2 : ℝ) ≤ 0 + 0) h0

#print axioms solution
