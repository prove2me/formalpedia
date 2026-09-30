-- Prove2me | solution 1 for lean_workbook_plus_14497
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:05:27.816122+00:00
-- url     : https://prove2.me/submissions/189f4b7c-5c63-4e53-a8bc-95b8119edd44

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (R r : ℝ) :
    9*R^2 - 20*R*r + 31*r^2 ≥ 16*R*r - 5*r^2 := by
  nlinarith [sq_nonneg (R - 2*r)]
