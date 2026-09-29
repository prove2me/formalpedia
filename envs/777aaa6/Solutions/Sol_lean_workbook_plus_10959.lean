-- Prove2me | solution 1 for lean_workbook_plus_10959
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:04.758036+00:00
-- url     : https://prove2.me/submissions/dbeac758-07fa-46d6-86ea-c38d42917092

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (h1 : a + b + c = 0) (h2 : abs a + abs b + abs c = 1) :
  a + b / 2 + c / 3 ≤ 1 / 3 := by
  intros
  grind
