-- Prove2me | solution 1 for lean_workbook_plus_12585
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:22:12.303168+00:00
-- url     : https://prove2.me/submissions/e57a4c00-2239-4e1c-b0cb-e459e5712045

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℂ) : 4 * x ^ 2 - 4 * x + 1 = 0 ↔ x = 1 / 2 ∨ x = 1 / 2 := by
  intros
  grind
