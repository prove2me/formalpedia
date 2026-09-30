-- Prove2me | solution 1 for lean_workbook_plus_37719
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:05.288834+00:00
-- url     : https://prove2.me/submissions/ae27eddc-ac2a-4c20-a992-cbb9d494f6fb

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (3 ^ 45 + 39 ≡ 0 [ZMOD 9]) := by
  norm_num [Int.ModEq]

#print axioms solution
