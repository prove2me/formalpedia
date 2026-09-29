-- Prove2me | solution 1 for lean_workbook_plus_53058
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:11:28.044021+00:00
-- url     : https://prove2.me/submissions/691a9f93-43e4-4aab-aab2-07224297cf2e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) (h : x + y + z = 0) : (x^4 + y^4 + z^4 = 2 * (x * y + y * z + z * x)^2 ∧ x^5 + y^5 + z^5 = -5 * x * y * z * (x * y + y * z + z * x)) := by
  intros
  grind
