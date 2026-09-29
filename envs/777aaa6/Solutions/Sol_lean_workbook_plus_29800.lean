-- Prove2me | solution 1 for lean_workbook_plus_29800
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:57:22.593643+00:00
-- url     : https://prove2.me/submissions/3433adc4-ce7e-42ce-b87e-3cc7e27ee83f

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (k : ℤ) (h : k % 2 = 1) : ∃ n : ℤ, k ^ 2 = 8 * n + 1 := by
  have hk : k%8=1 ∨ k%8=3 ∨ k%8=5 ∨ k%8=7 := by omega
  have hs : k^2%8=1 := by
    rcases hk with h|h|h|h <;> norm_num [pow_two,Int.mul_emod,h]
  refine ⟨k^2/8,?_⟩
  omega
