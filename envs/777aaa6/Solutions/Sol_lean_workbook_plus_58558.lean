-- Prove2me | solution 1 for lean_workbook_plus_58558
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:39:38.286746+00:00
-- url     : https://prove2.me/submissions/f7d05b98-5d83-4479-b68f-f0717cc4a746

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : 8^8^9 > 9^9^8 := by
  calc
    9^(9^8) < (8^3)^(9^8) := Nat.pow_lt_pow_left (by norm_num : 9 < (8 : ℕ)^3) (by positivity)
    _ = 8^(3*(9^8)) := (pow_mul _ _ _).symm
    _ < 8^(8^9) := Nat.pow_lt_pow_right (by norm_num : 1 < (8 : ℕ)) (by norm_num)
