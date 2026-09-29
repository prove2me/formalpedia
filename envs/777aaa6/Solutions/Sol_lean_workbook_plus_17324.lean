-- Prove2me | solution 1 for lean_workbook_plus_17324
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:52.887034+00:00
-- url     : https://prove2.me/submissions/acc2a7cf-0897-465d-8d86-6e521b445364

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (hab : a = -b) (hbc : b = -c) (hca : c = -a) : a = 0 ∧ b = 0 ∧ c = 0 := by
  intros
  grind
