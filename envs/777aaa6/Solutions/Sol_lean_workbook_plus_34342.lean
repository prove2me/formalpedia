-- Prove2me | solution 1 for lean_workbook_plus_34342
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:33:46.176027+00:00
-- url     : https://prove2.me/submissions/de4bc3e9-f07b-4fea-b012-0e8e0f99a7e8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (b : ℝ) (h : b * (b + 1) = 0) : b = 0 ∨ b = -1 := by
  intros
  grind
