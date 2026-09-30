-- Prove2me | solution 1 for lean_workbook_plus_33575
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:04:15.225905+00:00
-- url     : https://prove2.me/submissions/c09bbb17-442b-4f9a-8d26-1cfa02d1436d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (x : ℝ) : x^4 - 8*x + 8 ≥ 0 := by
  nlinarith [sq_nonneg (x^2 - 2), sq_nonneg (x - 1)]
