-- Prove2me | solution 1 for lean_workbook_plus_28386
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:07.619674+00:00
-- url     : https://prove2.me/submissions/3babdc9d-d876-4fa5-b52b-b54ffa772178

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (h : (2017 * 2018 - 2016 * 2019) * x * (x - 4035) = 0) : x = 0 ∨ x = 4035 := by
  intros
  grind
