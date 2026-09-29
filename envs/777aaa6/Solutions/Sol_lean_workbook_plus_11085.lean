-- Prove2me | solution 1 for lean_workbook_plus_11085
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:54.593682+00:00
-- url     : https://prove2.me/submissions/c463b381-6ead-4fe0-b37d-173bcaa60406

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ)
  (h₀ : 2 / 3 * 10 / 8 = 1 / 2 * 5 / x) :
  x = 3 := by
  intros
  grind
