-- Prove2me | solution 1 for lean_workbook_plus_34462
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:14:39.037559+00:00
-- url     : https://prove2.me/submissions/39a8f42e-3153-48ce-a246-6a935cf7d74e

import Mathlib
set_option autoImplicit false

theorem solution (k : ℕ) (h : k > 0) : (3 : ℝ)^k >= 1 + 2 * k   := by
  simpa only [show (1 : ℝ) + 2 = 3 by norm_num, mul_comm] using
    (one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 2) k)

#print axioms solution
