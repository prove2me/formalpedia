-- Prove2me | solution 1 for lean_workbook_plus_3213
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:45:34.583311+00:00
-- url     : https://prove2.me/submissions/01e16d13-0cc0-4721-bc0d-943afebe2190

import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℤ) : n ^ 2 ≡ 1 [ZMOD 5] ↔ n ≡ 1 [ZMOD 5] ∨ n ≡ -1 [ZMOD 5] := by
  have hp := ((Int.mod_modEq n 5).pow 2).eq
  simp only [Int.ModEq]
  rw [← hp]
  have hn := Int.emod_nonneg n (by decide : (5:ℤ) ≠ 0)
  have hn' := Int.emod_lt_of_pos n (by decide : (0:ℤ) < 5)
  interval_cases h : n % 5 <;> norm_num [h]
