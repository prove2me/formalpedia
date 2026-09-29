-- Prove2me | solution 1 for lean_workbook_plus_42173
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:42.734096+00:00
-- url     : https://prove2.me/submissions/df6fe9e4-5534-4f1e-ae85-688384f4a148

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (c : ℝ) : √(c^2 - (c - 1)^2) = √(2 * c - 1) := by
  intros
  grind
