-- Prove2me | solution 1 for lean_workbook_plus_41740
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:52.741799+00:00
-- url     : https://prove2.me/submissions/2d777ea3-8215-4e34-a777-7e92e3112497

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a : ℝ) (h₁ : a^2 - 2*a + 2 = 11) : a = 1 - Real.sqrt 10 ∨ a = 1 + Real.sqrt 10 := by
  intros
  grind
