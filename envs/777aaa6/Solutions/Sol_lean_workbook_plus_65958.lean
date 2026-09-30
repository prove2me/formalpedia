-- Prove2me | solution 1 for lean_workbook_plus_65958
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:18:11.569987+00:00
-- url     : https://prove2.me/submissions/a9ccc4c0-149a-4724-b884-fe6994eac074

import Mathlib
set_option autoImplicit false

theorem solution (n : ℕ) (h₁ : 6 ≤ n) : (n + 3) ^ 3 ≤ 3 ^ n   := by
  rw [pow_three]
  induction' h₁ with k hk
  norm_num
  rw [pow_succ]
  nlinarith

#print axioms solution
