-- Prove2me | solution 1 for lean_workbook_plus_78853
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:12:57.572132+00:00
-- url     : https://prove2.me/submissions/b1f7451a-8770-4fc4-baba-590eb9c92db3

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : |x - ⌊x⌋ - 1 / 2| ≤ 1 / 2 := by
  rw [abs_le]
  constructor <;> linarith [Int.floor_le x, Int.lt_floor_add_one x]

#print axioms solution
