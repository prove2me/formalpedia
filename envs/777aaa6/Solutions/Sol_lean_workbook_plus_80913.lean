-- Prove2me | solution 1 for lean_workbook_plus_80913
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:19:08.041701+00:00
-- url     : https://prove2.me/submissions/d515fdec-ee58-4d1c-a2a4-fd55be5cdf10

import Mathlib

theorem solution (a x y : ℝ) (ha : a > 0)
    (hx : |x - 1| < a / 3) (hy : |y - 2| < a / 3) : |2 * x + y - 4| < a := by
  obtain ⟨hx1, hx2⟩ := abs_lt.mp hx
  obtain ⟨hy1, hy2⟩ := abs_lt.mp hy
  apply abs_lt.mpr
  constructor <;> linarith
