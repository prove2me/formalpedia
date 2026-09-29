-- Prove2me | solution 1 for lean_workbook_plus_51822
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:29:14.772302+00:00
-- url     : https://prove2.me/submissions/ed1f5d8f-8ac9-41d2-b139-2bf5a9ed44bf

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) : (a + b) * (b + c) * (c + d) * (d + a) ≥ (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b) := by
  intros
  nlinarith [sq_nonneg (a*b - c*d), sq_nonneg (a*c - b*d), sq_nonneg (a*d - b*c)]
