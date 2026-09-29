-- Prove2me | solution 1 for lean_workbook_plus_55012
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:49:48.920289+00:00
-- url     : https://prove2.me/submissions/13371d7f-67fa-4323-aa74-e02751c61595

import Mathlib.Tactic.NormNum
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℤ, a ∣ (a + 1) * (b + 1) * (c + 1) - (b + c) * (a + 1)) := by
  intro h
  have h0 := h 0 0 0
  norm_num at h0
