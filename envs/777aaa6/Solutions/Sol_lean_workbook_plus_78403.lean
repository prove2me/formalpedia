-- Prove2me | solution 1 for lean_workbook_plus_78403
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:58:01.592625+00:00
-- url     : https://prove2.me/submissions/92d5ee81-4dc1-4e6f-9912-a857b834fdc6

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem solution (a b : ℝ) (n : ℕ) :
    a = (2 + Real.sqrt 5)^(2 * n) ∧ b = (2 - Real.sqrt 5)^(2 * n) →
      (a^3 + b^3) / (a + b) = a^2 - a * b + b^2 := by
  rintro ⟨ha, hb⟩
  have hbase : 0 < 2 + Real.sqrt 5 := by nlinarith [Real.sqrt_nonneg 5]
  have hap : 0 < a := by rw [ha]; exact pow_pos hbase _
  have hbp : 0 ≤ b := by
    rw [hb, pow_mul]
    exact pow_nonneg (sq_nonneg (2 - Real.sqrt 5)) n
  apply (div_eq_iff (ne_of_gt (add_pos_of_pos_of_nonneg hap hbp))).2
  ring
