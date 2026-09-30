-- Prove2me | solution 1 for lean_workbook_plus_4137
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:04:16.613838+00:00
-- url     : https://prove2.me/submissions/2f0a82c5-4de6-447f-966d-17333156a117

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (x : ℝ) : x^4 + 1 ≥ 2*x^2 := by
  nlinarith [sq_nonneg (x^2 - 1)]
