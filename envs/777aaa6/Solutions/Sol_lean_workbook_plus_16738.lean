-- Prove2me | solution 1 for lean_workbook_plus_16738
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:27.341624+00:00
-- url     : https://prove2.me/submissions/afddb508-1bf5-4d92-bbc4-ce59c3dab863

import Mathlib.Analysis.Complex.Basic

theorem solution (x n : ℤ) (hpos : 0 < x) (hrelprime : (x.gcd n) = 1) : ∃ k, n ∣ x^k - 1 :=
  ⟨0, by simp⟩
