-- Prove2me | solution 1 for lean_workbook_plus_77961
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:09:57.148565+00:00
-- url     : https://prove2.me/submissions/a7af4f93-8026-433d-a7dd-cd315b3ef7fb

import Mathlib

set_option autoImplicit false

theorem solution : ∀ a : ℤ,
    a ^ 3 + (a + 1) ^ 3 + (a + 2) ^ 3 = 3 * a ^ 3 + 9 * a ^ 2 + 15 * a + 9 ∧
    3 * a + 3 ∣ 3 * a ^ 3 + 9 * a ^ 2 + 15 * a + 9 ∧
    (3 * a + 3) * (a ^ 2 + 2 * a + 3) = 3 * a ^ 3 + 9 * a ^ 2 + 15 * a + 9 ∧
    a ^ 2 + 2 * a + 3 = a ^ 2 + 2 * a + 3 ∧
    (3 * a + 3) * (a ^ 2 + 2 * a + 3) = 3 * a ^ 3 + 9 * a ^ 2 + 15 * a + 9 := by
  intro a
  refine ⟨by ring, ⟨a ^ 2 + 2 * a + 3, by ring⟩, by ring, rfl, by ring⟩
