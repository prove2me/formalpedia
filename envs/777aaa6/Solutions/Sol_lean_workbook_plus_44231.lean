-- Prove2me | solution 1 for lean_workbook_plus_44231
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:38.783655+00:00
-- url     : https://prove2.me/submissions/08b40391-6c4a-4325-9bc6-dfacb3824477

import Mathlib
set_option autoImplicit false

theorem solution  (n : ℕ)
  (h₀ : 5^n = 3125) :
  n = 5   := by
  rw [show 3125 = 5^5 by norm_num] at h₀
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 5) h₀

#print axioms solution
