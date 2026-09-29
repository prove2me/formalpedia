-- Prove2me | solution 1 for lean_workbook_plus_12276
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:06:36.794905+00:00
-- url     : https://prove2.me/submissions/8b525b41-4fa1-4c99-925f-1816b66818c0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y z μ : ℝ) : (μ^2 + 1) * (x^4 + y^2 * z^2) ≥ (μ * x^2 + y * z)^2 := by
  nlinarith [sq_nonneg (x ^ 2 - μ * y * z)]
