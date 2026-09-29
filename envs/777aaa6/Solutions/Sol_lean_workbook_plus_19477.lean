-- Prove2me | solution 1 for lean_workbook_plus_19477
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:25.987741+00:00
-- url     : https://prove2.me/submissions/493d58ed-6220-4d9e-b847-9dd541281765

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a : ℝ) :
  a^4 - a^3 - a + 1 ≥ 0 := by
  intros
  
  have h_identity : (a^4 - a^3 - a + 1) - (0) = (1 : ℝ) * 1 * ((1 + ((-1 / 2) * a) + ((-1 / 2) * (a ^ 2))))^2 + ((3 / 4) : ℝ) * 1 * ((a + ((-1) * (a ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a^4 - a^3 - a + 1) - (0) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
