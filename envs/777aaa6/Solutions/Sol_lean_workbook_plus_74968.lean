-- Prove2me | solution 1 for lean_workbook_plus_74968
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:59.794086+00:00
-- url     : https://prove2.me/submissions/442b2296-8e2a-438a-8016-225c09ad132f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : 34 * x ^ 2 - 13 * x - 21 = 0 ↔ x = -21 / 34 ∨ x = 1 := by
  intros
  grind
