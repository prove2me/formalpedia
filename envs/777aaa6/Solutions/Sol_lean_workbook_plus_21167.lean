-- Prove2me | solution 1 for lean_workbook_plus_21167
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:20:39.259582+00:00
-- url     : https://prove2.me/submissions/e624da81-d54e-4ef6-835f-7f35a0370281

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) : (3*x + 4*y - 31 = 0 ∧ 4*x - 3*y - 33 = 0) ↔ x = 9 ∧ y = 1 := by
  intros
  grind
