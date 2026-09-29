-- Prove2me | solution 1 for lean_workbook_plus_14433
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:22.729744+00:00
-- url     : https://prove2.me/submissions/2dde8aaf-14a0-453c-a779-ee959e59ee00

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (h₁ : a + b + c = 6) (h₂ : a * b + b * c + c * a = 9) : (a - 1) ^ 2 + (b - 1) ^ 2 + (c - 1) ^ 2 = 9 := by
  intros
  nlinarith
