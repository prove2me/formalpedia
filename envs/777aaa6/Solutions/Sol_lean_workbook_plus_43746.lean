-- Prove2me | solution 1 for lean_workbook_plus_43746
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:19:55.602609+00:00
-- url     : https://prove2.me/submissions/de742131-f815-4c03-be9f-05eb93fabba8

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℤ) : ∃ m n : ℤ, x / 2 = m / n ∧ m.gcd n = 1 :=
  ⟨x / 2, 1, by simp, by simp⟩
