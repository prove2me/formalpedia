-- Prove2me | solution 1 for lean_workbook_plus_78640
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:19:29.501513+00:00
-- url     : https://prove2.me/submissions/8f1bb707-b628-4557-b52a-1513975a6c63

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution (a : ℕ → ℝ) (n : ℕ)
    (ha : a (n + 1) = a n ^ 2 / (a n ^ 2 - a n + 1)) :
    a (n + 1) ≤ 4 * a n ^ 2 / 3 := by
  have hd : 0 < a n ^ 2 - a n + 1 := by nlinarith [sq_nonneg (a n - 1 / 2)]
  rw [ha]
  apply (div_le_div_iff₀ hd (by norm_num : (0 : ℝ) < 3)).mpr
  nlinarith [mul_nonneg (sq_nonneg (a n)) (sq_nonneg (2 * a n - 1))]

#print axioms solution
