-- Prove2me | solution 1 for lean_workbook_plus_71945
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:12:56.416561+00:00
-- url     : https://prove2.me/submissions/59e20c09-2313-486b-a385-075f55577f93

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (z : ℂ) (h : z = (24 + 7 * Complex.I) / 25) : z = (24 / 25) + (7 / 25) * Complex.I := by
  intros
  grind
