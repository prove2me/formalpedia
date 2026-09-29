-- Prove2me | solution 1 for lean_workbook_plus_57089
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:36:47.07694+00:00
-- url     : https://prove2.me/submissions/cc4f27d0-00c6-4092-857e-82ea15e8559e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (b c : ℝ) : (b^2 + 2) * (c^2 + 2) ≥ 3 * (1 + (b + c)^2 / 2) ↔ (b * c - 1)^2 + (b - c)^2 / 2 ≥ 0 := by
  intros
  grind
