-- Prove2me | solution 1 for lean_workbook_plus_12234
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:43.994627+00:00
-- url     : https://prove2.me/submissions/44700fd5-e7fc-4fea-bc39-9ce3743ef390

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) : (x^2 + y^2 + (x + y)^2) * ((x - y)^4 + (2 * x + y)^4 + (2 * y + x)^4) ≥ ((x + y)^2 / 2 + (x + y)^2) * (2 * (2 * x + y)^2 * (2 * y + x)^2) := by
  intros
  nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x^3 - y^3)]
