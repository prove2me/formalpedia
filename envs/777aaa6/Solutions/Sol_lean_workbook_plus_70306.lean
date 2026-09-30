-- Prove2me | solution 1 for lean_workbook_plus_70306
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:00:14.279281+00:00
-- url     : https://prove2.me/submissions/24581e5f-aee6-4cae-867f-1875a7eb8200

import Mathlib
set_option autoImplicit false

theorem solution : ∀ a : ℝ,
    (2 * (1 - a + a ^ 2) ^ 2 ≥ 1 + a ^ 4 ↔ (1 - a) ^ 4 ≥ 0) := by
  intro a
  have he : 2 * (1 - a + a ^ 2) ^ 2 - (1 + a ^ 4) = (1 - a) ^ 4 := by ring
  constructor <;> intro h <;> nlinarith [he]

#print axioms solution
