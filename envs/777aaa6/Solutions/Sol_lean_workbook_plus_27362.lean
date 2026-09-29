-- Prove2me | solution 1 for lean_workbook_plus_27362
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:57:04.5659+00:00
-- url     : https://prove2.me/submissions/6ba76475-532b-4d37-9952-c6ebce7cc401

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ)
  (ma mb mc : ℝ) :
  (a * ma + b * mb + c * mc)^2 ≤ (a^2 + b^2 + c^2) * (ma^2 + mb^2 + mc^2) := by
  nlinarith [sq_nonneg (a*mb-b*ma), sq_nonneg (a*mc-c*ma), sq_nonneg (b*mc-c*mb)]
