-- Prove2me | solution 1 for lean_workbook_plus_20796
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:57:10.520344+00:00
-- url     : https://prove2.me/submissions/4dea5605-2830-4831-bcc0-ec689f804d82

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (z : ℤ) : (z = ⌊x⌋) → z ≤ x ∧ x < z + 1 := by
  intros
  exact?
