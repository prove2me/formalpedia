-- Prove2me | solution 1 for lean_workbook_plus_39229
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:25:52.221476+00:00
-- url     : https://prove2.me/submissions/047f1c6c-4449-4cc4-b71a-8ad86d8e9552

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x_A y_A : ℝ) (h : x_A > 0 ∧ y_A > 0) : (x_A / y_A = 1 ↔ x_A = y_A) := by
  intros
  grind
