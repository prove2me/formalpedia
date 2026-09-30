-- Prove2me | solution 1 for lean_workbook_plus_72139
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:16.059905+00:00
-- url     : https://prove2.me/submissions/b7173684-37c6-4a52-9633-487dbab53d42

import Mathlib

set_option autoImplicit false

theorem solution (x : ℝ) : x + 3 ≥ 0 ↔ x ≥ -3 := by
  constructor <;> intro h <;> linarith
