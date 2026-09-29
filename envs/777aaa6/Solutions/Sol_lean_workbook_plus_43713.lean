-- Prove2me | solution 1 for lean_workbook_plus_43713
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:46:21.390108+00:00
-- url     : https://prove2.me/submissions/eab04b20-4c67-4fd3-8fd1-cef63767373e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (p x : ℝ) : ∃ f : ℝ → ℝ, f x = p * x + 1 - p / 2 := by
  intros
  aesop (config := {maxRuleApplications := 120})
