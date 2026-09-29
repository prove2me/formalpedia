-- Prove2me | solution 1 for lean_workbook_plus_16061
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:35.070459+00:00
-- url     : https://prove2.me/submissions/91390cac-b9ff-42e3-b65b-6d843aa95159

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : -3 < 2*x - 5 ∧ 2*x - 5 < 7 ↔ 1 < x ∧ x < 6 := by
  intros
  grind
