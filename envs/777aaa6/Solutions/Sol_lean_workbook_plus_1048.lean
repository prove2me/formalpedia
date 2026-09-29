-- Prove2me | solution 1 for lean_workbook_plus_1048
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:00:25.476774+00:00
-- url     : https://prove2.me/submissions/fdc02bff-6687-4b02-9a78-b66af9b09292

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : (1 / 9) * (2 * a ^ 2 + 2 * c ^ 2 - b ^ 2 + 2 * a ^ 2 + 2 * b ^ 2 - c ^ 2) = a ^ 2 ↔ b ^ 2 + c ^ 2 = 5 * a ^ 2 := by
  intros
  grind
