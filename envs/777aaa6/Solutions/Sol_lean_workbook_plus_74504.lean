-- Prove2me | solution 1 for lean_workbook_plus_74504
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:00.216706+00:00
-- url     : https://prove2.me/submissions/6132268a-f5fd-4ef4-94d5-921622210c72

import Mathlib

set_option autoImplicit false

theorem solution (x y : ℝ) : 5 * x + 12 * y = 41 ↔ y = (-5 / 12) * x + 41 / 12 := by
  constructor <;> intro h <;> linarith
