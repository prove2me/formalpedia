-- Prove2me | solution 1 for lean_workbook_plus_65631
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:40.898851+00:00
-- url     : https://prove2.me/submissions/6c24162f-c2ad-43d9-8554-96940cd95fdc

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ k : ℕ, k^3 < 61 → k ∈ ({1, 2, 3} : Finset ℕ)) := by
  intro h
  have bad := h 0 (by norm_num)
  norm_num at bad

#print axioms solution
