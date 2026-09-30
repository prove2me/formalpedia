-- Prove2me | solution 1 for lean_workbook_plus_63825
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:43:19.112359+00:00
-- url     : https://prove2.me/submissions/98aec2b3-1237-4e29-b8cf-e388fc47c2b3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    a * b / (a + b) + c * d / (c + d) ≤ (a + c) * (b + d) / (a + b + c + d) := by
  have hab : 0 < a + b := by positivity
  have hcd : 0 < c + d := by positivity
  have hs : 0 < a + b + c + d := by positivity
  have hid :
      ((a + c) * (b + d) / (a + b + c + d) -
        (a * b / (a + b) + c * d / (c + d))) *
        ((a + b) * (c + d) * (a + b + c + d)) = (a * d - b * c) ^ 2 := by
    field_simp [ne_of_gt hab, ne_of_gt hcd, ne_of_gt hs]
    <;> ring
  apply sub_nonneg.mp
  apply nonneg_of_mul_nonneg_left (b := (a + b) * (c + d) * (a + b + c + d))
    (by rw [hid]; exact sq_nonneg _) (by positivity)

#print axioms solution
