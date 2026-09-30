-- Prove2me | solution 1 for lean_workbook_plus_40882
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:32.532906+00:00
-- url     : https://prove2.me/submissions/3931ce55-5747-4c32-ad7f-fd7b6cdf06e6

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) : (2*x + y ≤ 10 ∧ 5*x + 2*y ≥ 20 ∧ -x + 2*y ≥ 0 ∧ x >= 0 ∧ y >= 0) → x + 3*y >= 7 := by
  rintro ⟨h1, h2, h3, h4, h5⟩
  linarith
