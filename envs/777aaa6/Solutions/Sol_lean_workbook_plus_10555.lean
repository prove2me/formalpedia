-- Prove2me | solution 1 for lean_workbook_plus_10555
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:58:04.611603+00:00
-- url     : https://prove2.me/submissions/9d9ec237-130b-4404-b738-b4b2dcbd6e26

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) : |(abs a) - (abs b)| ≤ abs (a - b) := by
  intros
  exact abs_abs_sub_abs_le a b
