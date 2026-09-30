-- Prove2me | solution 1 for lean_workbook_plus_39579
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:04.411629+00:00
-- url     : https://prove2.me/submissions/695301ea-9d9f-4426-bc3d-6c8d472ec171

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) : 4 ≤ |x + 1| + |x - 2| + |x - 3| := by
  rcases abs_cases (x + 1) with h1 | h1 <;>
  rcases abs_cases (x - 2) with h2 | h2 <;>
  rcases abs_cases (x - 3) with h3 | h3 <;>
  linarith
