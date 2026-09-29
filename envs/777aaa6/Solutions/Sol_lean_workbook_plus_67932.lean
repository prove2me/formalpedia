-- Prove2me | solution 1 for lean_workbook_plus_67932
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:46.421308+00:00
-- url     : https://prove2.me/submissions/55984ec2-1339-4e5a-8967-4f1a629913d0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) : (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) ↔ 3 * (a + b) * (a - b) ^ 2 ≥ 0 := by
  intros
  grind
