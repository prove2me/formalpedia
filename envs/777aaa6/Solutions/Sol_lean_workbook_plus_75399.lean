-- Prove2me | solution 1 for lean_workbook_plus_75399
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:49:09.186016+00:00
-- url     : https://prove2.me/submissions/204e857b-4b7b-4c26-921c-0b5fd058e132

import Mathlib
set_option autoImplicit false

theorem solution : 2022 ^ 2022 ≡ 0 [ZMOD 9]   := by
  have h : (2022 : ℤ) ^ 2 ≡ 0 [ZMOD 9] := by norm_num [Int.ModEq]
  simpa only [← pow_mul, zero_pow (by norm_num : (1011 : ℕ) ≠ 0)] using (Int.ModEq.pow 1011 h)

#print axioms solution
