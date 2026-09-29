-- Prove2me | solution 1 for lean_workbook_plus_848
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:35.256632+00:00
-- url     : https://prove2.me/submissions/e638b248-7501-41a0-af98-865164858d4e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ) (x : Fin n → ℝ) : 
  |∑ i, x i| ≤ ∑ i, |x i| := by
  intros
  exact?
