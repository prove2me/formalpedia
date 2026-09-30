-- Prove2me | solution 1 for lean_workbook_plus_71683
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:32.883949+00:00
-- url     : https://prove2.me/submissions/13ad230b-e4ec-4728-bb3f-dce7de8e0e1d

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ f : ℝ → ℝ, ∀ x, f x = x + 1) := by
  intro h
  have h0 := h (fun _ => 0) 0
  norm_num at h0

#print axioms solution
