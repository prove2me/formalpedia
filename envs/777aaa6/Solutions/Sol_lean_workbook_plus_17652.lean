-- Prove2me | solution 1 for lean_workbook_plus_17652
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:27.386986+00:00
-- url     : https://prove2.me/submissions/5336735d-d7da-4983-94b2-2a4719713b91

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : |x| > Real.sqrt 2 ↔ x < -Real.sqrt 2 ∨ x > Real.sqrt 2 := by
  intros
  grind
