-- Prove2me | solution 1 for lean_workbook_plus_71644
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:32.094259+00:00
-- url     : https://prove2.me/submissions/d02a0658-f5cb-4c4b-acc1-e4d7098948f8

import Mathlib
set_option autoImplicit false

theorem solution : ¬ ((11 : ℤ) ^ 1 ≡ 1 [ZMOD 100]) := by
  norm_num [Int.ModEq]

#print axioms solution
