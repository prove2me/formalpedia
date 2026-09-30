-- Prove2me | solution 1 for lean_workbook_plus_14391
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:49:19.580228+00:00
-- url     : https://prove2.me/submissions/9a439a1b-fca6-4b63-8192-63b9bf36c9b6

import Mathlib
set_option autoImplicit false

theorem solution  (x y : ℝ) :
  1 + |x * y - 1| ≤ (1 + |x - 1|) * (1 + |y - 1|)   := by
  have he : x * y - 1 = (x - 1) + (y - 1) + (x - 1) * (y - 1) := by ring
  have ht : |x * y - 1| ≤ |x - 1| + |y - 1| + |x - 1| * |y - 1| := by
    rw [he]
    calc
      |(x - 1) + (y - 1) + (x - 1) * (y - 1)| ≤
          |(x - 1) + (y - 1)| + |(x - 1) * (y - 1)| := abs_add_le _ _
      _ ≤ (|x - 1| + |y - 1|) + |(x - 1) * (y - 1)| :=
        add_le_add (abs_add_le _ _) (le_refl _)
      _ = |x - 1| + |y - 1| + |x - 1| * |y - 1| := by rw [abs_mul]
  calc
    1 + |x * y - 1| ≤ 1 + (|x - 1| + |y - 1| + |x - 1| * |y - 1|) := add_le_add (le_refl 1) ht
    _ = (1 + |x - 1|) * (1 + |y - 1|) := by ring

#print axioms solution
