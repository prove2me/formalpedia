-- Prove2me | solution 1 for lean_workbook_plus_26687
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:44.280621+00:00
-- url     : https://prove2.me/submissions/dbc8fa45-acc4-4811-85c9-957e761fb280

import Mathlib
set_option autoImplicit false

theorem solution (a b n : ℤ) (hn : n ≠ 0) : a % n = b % n ↔ n ∣ a - b   := by
  change Int.ModEq n a b ↔ n ∣ a-b
  rw [Int.modEq_comm, Int.modEq_iff_dvd]

#print axioms solution
