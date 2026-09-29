-- Prove2me | solution 1 for lean_workbook_plus_68415
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:54:01.341339+00:00
-- url     : https://prove2.me/submissions/f901a8c5-1fd6-4e7e-804f-7c897f9e5367

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (hx: x ≠ 0) : (2017 * 2018 - 2016 * 2019) * x ^ 2 - (2017 * 2018 - 2016 * 2019) * 4035 * x = 0 ↔ x = 0 ∨ x = 4035 := by
  intros
  grind
