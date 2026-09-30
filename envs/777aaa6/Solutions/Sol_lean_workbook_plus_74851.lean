-- Prove2me | solution 1 for lean_workbook_plus_74851
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:48:44.689429+00:00
-- url     : https://prove2.me/submissions/92d947b6-4800-488e-b125-1f00d1db134d

import Mathlib
set_option autoImplicit false

theorem solution : ∃ r s : ℂ, r + s = 0 ∧ r * s = -9   := by
  refine ⟨(3 : ℂ), (-3 : ℂ), by norm_num, by norm_num⟩

#print axioms solution
