-- Prove2me | solution 1 for lean_workbook_plus_31690
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:40.344535+00:00
-- url     : https://prove2.me/submissions/e3891b9f-4fe5-43ff-aeb6-557fb387c757

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) : |x| + |y| = |(x + y) / 2 + (x - y) / 2| + |(x + y) / 2 - (x - y) / 2| := by
  intros
  grind
