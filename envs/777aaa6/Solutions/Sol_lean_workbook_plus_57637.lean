-- Prove2me | solution 1 for lean_workbook_plus_57637
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:54:46.86157+00:00
-- url     : https://prove2.me/submissions/4e5560ae-1905-4b51-807c-9477ef5bcd07

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ) (x : Fin n → ℝ) : |∑ i, x i| ≤ ∑ i, |x i| := by
  intros
  exact?
