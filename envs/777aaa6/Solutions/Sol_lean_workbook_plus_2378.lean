-- Prove2me | solution 1 for lean_workbook_plus_2378
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:57:14.247807+00:00
-- url     : https://prove2.me/submissions/e9e423cf-7e61-43af-9a53-a21aafc9cf8f

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ n : ℤ, n ^ 2 ≡ 0 [ZMOD 4] ∨ n ^ 2 ≡ 1 [ZMOD 4] := by
  intro n
  have hn : 0 ≤ n % 4 ∧ n % 4 < 4 := ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  have h : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases h with h | h | h | h <;> norm_num [Int.ModEq, pow_two, Int.mul_emod, h]
