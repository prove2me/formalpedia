-- Prove2me | solution 1 for lean_workbook_plus_1523
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:46.765527+00:00
-- url     : https://prove2.me/submissions/dc8cc1bf-f233-437d-a6f7-6070e50e63af

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : 13 * a ^ 2 + 10 * b ^ 2 + 5 * c ^ 2 = 4 * a * b + 12 * b * c + 6 * a * c ↔ (2 * a - b) ^ 2 + (3 * b - 2 * c) ^ 2 + (3 * a - c) ^ 2 = 0 := by
  intros
  grind
