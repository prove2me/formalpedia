-- Prove2me | solution 1 for lean_workbook_plus_7674
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:47:33.920927+00:00
-- url     : https://prove2.me/submissions/e13ed7d3-bdad-45fd-862e-4d2773ea3f40

import Mathlib
set_option autoImplicit false

theorem solution (n : ℕ) : 10 ^ 4 - 1 ∣ 10 ^ (4 * n) - 1   := by
  simpa only [one_pow, pow_mul, pow_one] using Nat.sub_dvd_pow_sub_pow _ 1 n

#print axioms solution
