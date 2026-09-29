-- Prove2me | solution 1 for lean_workbook_plus_59599
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:31:33.626227+00:00
-- url     : https://prove2.me/submissions/92147e5f-e8ed-4c8a-8b38-6786417b5976

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (α β : ℝ) (k : ℝ) : α = (Real.sqrt (k + 3) + Real.sqrt (k - 1)) / 2 ∧ β = (Real.sqrt (k + 3) - Real.sqrt (k - 1)) / 2 ↔ α + β = Real.sqrt (k + 3) ∧ α - β = Real.sqrt (k - 1) := by
  intros
  grind
