-- Prove2me | solution 1 for lean_workbook_plus_44543
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:04:13.053086+00:00
-- url     : https://prove2.me/submissions/a8da1961-85a1-40f0-8dcb-18a5fc9d3ad3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (x : ℝ) : x^4 ≥ 4*x-3 := by
  nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x - 1)]
