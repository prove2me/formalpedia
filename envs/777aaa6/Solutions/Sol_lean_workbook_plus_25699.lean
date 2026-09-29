-- Prove2me | solution 1 for lean_workbook_plus_25699
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:30:46.462274+00:00
-- url     : https://prove2.me/submissions/89f14928-9be7-45f6-987d-e7aa33722afb

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) : (a + b) * (b + c) * (c + d) * (d + a) ≥ (a + b + c + d) * (a * c * d + a * b * d + a * b * c + b * c * d) := by
  intros
  nlinarith [sq_nonneg (a*b - c*d), sq_nonneg (a*c - b*d), sq_nonneg (a*d - b*c)]
