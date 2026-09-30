-- Prove2me | solution 1 for lean_workbook_plus_60118
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:02:32.429119+00:00
-- url     : https://prove2.me/submissions/d14eea23-8f05-495b-9869-c5de97e661a6

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c d : ℝ) : (a + b * Complex.I) * (c + d * Complex.I) = (a * c - b * d) + (a * d + b * c) * Complex.I := by
  apply Complex.ext <;> simp <;> ring
