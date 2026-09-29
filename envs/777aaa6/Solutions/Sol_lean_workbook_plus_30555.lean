-- Prove2me | solution 1 for lean_workbook_plus_30555
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:15:47.884712+00:00
-- url     : https://prove2.me/submissions/25884320-f397-4ca6-a652-bca3e1fc6d5e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : 9 * (x - 1) ^ 2 + 12 * x ≥ 8 * x ^ 2 ↔ (x - 3) ^ 2 ≥ 0 := by
  intros
  grind
