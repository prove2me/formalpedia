-- Prove2me | solution 1 for lean_workbook_plus_43733
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:39:40.743487+00:00
-- url     : https://prove2.me/submissions/5fdcbd7b-19e5-4ef4-b6bf-35c292a4f057

import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℕ) : x^2 ≡ 1 [ZMOD 5] ↔ x ≡ 1 [ZMOD 5] ∨ x ≡ 4 [ZMOD 5] := by
  have hi (z : ℤ) : z^2 ≡ 1 [ZMOD 5] ↔ z ≡ 1 [ZMOD 5] ∨ z ≡ 4 [ZMOD 5] := by
    have hp := ((Int.mod_modEq z 5).pow 2).eq
    simp only [Int.ModEq]
    rw [← hp]
    have hz := Int.emod_nonneg z (by decide : (5:ℤ) ≠ 0)
    have hz' := Int.emod_lt_of_pos z (by decide : (0:ℤ) < 5)
    interval_cases h : z % 5 <;> norm_num [h]
  simpa only [Int.natCast_pow] using hi x
