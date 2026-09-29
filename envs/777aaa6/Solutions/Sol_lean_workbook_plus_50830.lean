-- Prove2me | solution 1 for lean_workbook_plus_50830
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:13.703835+00:00
-- url     : https://prove2.me/submissions/8b5a1e64-bea7-459d-8611-dc140b08e605

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x^2 - 6*x + 8 = 0 ↔ x = 2 ∨ x = 4 := by
  intros
  grind
