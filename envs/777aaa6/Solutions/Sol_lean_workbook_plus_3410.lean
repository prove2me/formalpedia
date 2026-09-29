-- Prove2me | solution 1 for lean_workbook_plus_3410
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:20.624749+00:00
-- url     : https://prove2.me/submissions/e5dab4f4-9f7a-40ec-a712-be55fc3ecdee

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) : 2 * a ^ 2 + b ^ 2 ≥ 2 * Real.sqrt 2 * a * b := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hm := congrArg (fun t:ℝ => t*a^2) hs
  nlinarith [sq_nonneg (Real.sqrt 2*a-b)]
