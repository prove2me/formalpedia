-- Prove2me | solution 1 for lean_workbook_plus_81106
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:19:06.426047+00:00
-- url     : https://prove2.me/submissions/ee521c7a-7309-4875-95e2-b6efc3a92d97

import Mathlib

theorem solution (x y z : ℝ) : |x - y| + |y - z| + |z - x| ≥
    1 / 2 * (|x + y - 2 * z| + |y + z - 2 * x| + |z + x - 2 * y|) := by
  have htri (a b c : ℝ) : |a + b - 2*c| ≤ |a - c| + |b - c| := by
    calc
      _ = |(a-c) + (b-c)| := by congr 1; ring
      _ ≤ _ := abs_add_le (a-c) (b-c)
  have h1 := htri x y z
  have h2 := htri y z x
  have h3 := htri z x y
  rw [abs_sub_comm x z] at h1
  rw [abs_sub_comm y x] at h2
  rw [abs_sub_comm z y] at h3
  linarith
