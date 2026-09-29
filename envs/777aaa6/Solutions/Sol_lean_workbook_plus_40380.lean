-- Prove2me | solution 1 for lean_workbook_plus_40380
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:59:24.219275+00:00
-- url     : https://prove2.me/submissions/1438d8d6-f7e2-40dd-b192-f8ea59d36f36

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : 360 * (x + 4) = 400 * x + 640 ↔ x = 20 := by
  intros
  grind
