-- Prove2me | solution 1 for lean_workbook_plus_70069
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:49:31.578915+00:00
-- url     : https://prove2.me/submissions/0833eae5-acca-4de1-856f-af89324a1a1e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x^2 + 3*x + 2 = 0 ↔ x = -1 ∨ x = -2 := by
  intros
  grind
