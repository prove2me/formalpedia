-- Prove2me | solution 1 for lean_workbook_plus_3467
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:40.716617+00:00
-- url     : https://prove2.me/submissions/89e25ff5-9c2e-4f8e-8c61-8ffb608339ef

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) : a / b + (a - b) / (a / b) = a / b + b * (a - b) / a := by
  intros
  grind
