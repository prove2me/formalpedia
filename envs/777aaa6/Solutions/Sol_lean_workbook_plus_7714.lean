-- Prove2me | solution 1 for lean_workbook_plus_7714
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:34.029502+00:00
-- url     : https://prove2.me/submissions/bd6ec1cb-1b8a-4283-90ce-9f719a79a105

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) : x + 2*y = 5 ↔ y = -0.5*x + 2.5 := by
  constructor <;> intro h <;> linarith
