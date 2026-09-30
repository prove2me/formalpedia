-- Prove2me | solution 1 for lean_workbook_plus_81050
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:39:38.942701+00:00
-- url     : https://prove2.me/submissions/297ffada-4270-4563-b4ab-bfa781664df1

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (x : ℝ) (h₀ : 0 < x) :
    1 / (4 * x ^ 2 + 1) ≥ -8 * x / 25 + 13 / 25 := by
  have hd : 0 < 4 * x ^ 2 + 1 := by nlinarith [sq_nonneg x]
  apply (le_div_iff₀ hd).mpr
  have hp : 0 ≤ (x - 1) ^ 2 * (8 * x + 3) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith

theorem equality_case (x : ℝ) (hx : 0 < x) :
    1 / (4 * x ^ 2 + 1) = -8 * x / 25 + 13 / 25 ↔ x = 1 := by
  have hd : 0 < 4 * x ^ 2 + 1 := by nlinarith [sq_nonneg x]
  constructor
  · intro h
    have hm := (div_eq_iff hd.ne').mp h
    have hz : (x - 1) ^ 2 * (8 * x + 3) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with hs | hl
    · nlinarith [sq_nonneg (x - 1)]
    · linarith
  · rintro rfl
    norm_num

#print axioms solution
#print axioms equality_case
