-- Prove2me | solution 1 for lean_workbook_plus_61257
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:18:19.390078+00:00
-- url     : https://prove2.me/submissions/7db89b06-32fd-408c-b25f-5ea0daf93f77

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) : 9 * (a ^ 6 + b ^ 6 + c ^ 6) + 6 * a ^ 2 * b ^ 2 * c ^ 2 ≥ 7 * (a ^ 3 * b ^ 3 + b ^ 3 * c ^ 3 + c ^ 3 * a ^ 3) + 4 * a * b * c * (a ^ 3 + b ^ 3 + c ^ 3) := by
  nlinarith only [sq_nonneg (a^3-b^3), sq_nonneg (b^3-c^3), sq_nonneg (c^3-a^3), sq_nonneg (a^3+b^3+c^3-3*a*b*c)]
