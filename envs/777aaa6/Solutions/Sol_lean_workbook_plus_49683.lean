-- Prove2me | solution 1 for lean_workbook_plus_49683
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:16:17.195828+00:00
-- url     : https://prove2.me/submissions/ae39afad-a895-4e29-aa18-6390c9f31a97

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (hx : x ≠ -2) : (2 * x + 5) / (x + 2) = 2 + 1 / (x + 2) := by
  intros
  grind
