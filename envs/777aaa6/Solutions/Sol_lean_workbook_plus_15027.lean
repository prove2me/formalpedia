-- Prove2me | solution 1 for lean_workbook_plus_15027
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:51:44.215545+00:00
-- url     : https://prove2.me/submissions/2adfca81-1813-44e8-bf0e-798a883b766f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) (hab : a * b = 1) (h : a * c + b * d = 2) :
  c * d ≤ 1 := by
  intros
  nlinarith [sq_nonneg (a*b - c*d), sq_nonneg (a*c - b*d), sq_nonneg (a*d - b*c)]
