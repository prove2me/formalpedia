-- Prove2me | solution 1 for lean_workbook_plus_70186
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:20:30.177291+00:00
-- url     : https://prove2.me/submissions/49dabb8b-c46a-4b44-94bf-99b0b0386a66

import Mathlib.Analysis.Complex.Basic

theorem solution (n a b : ℤ) (h1 : n ∣ a) (h2 : n ∣ b) : n ∣ a + b := by
  exact Int.dvd_add h1 h2
