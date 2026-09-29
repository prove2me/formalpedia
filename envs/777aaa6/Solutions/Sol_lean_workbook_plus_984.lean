-- Prove2me | solution 1 for lean_workbook_plus_984
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:57:15.789991+00:00
-- url     : https://prove2.me/submissions/15bca946-971b-4d38-ae9b-750dc1811319

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a : ℝ, a ≠ 0 ∧ a ≠ -1 → 1/a = 1/(a + 1) + 1/(a*(a + 1)) := by
  intro a
  intros
  grind
