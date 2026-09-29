-- Prove2me | solution 1 for lean_workbook_plus_45324
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:46:34.301021+00:00
-- url     : https://prove2.me/submissions/6b879d2e-9e40-4c7f-bad0-530ad2856b91

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c: ℝ) : (a^2+b^2+c^2)^2 ≥ (a+b+c)*(a*b*(a+b) + b*c*(b+c) + c*a*(c+a) - 3*a*b*c) ↔ a^4+b^4+c^4+(a*b*c)*(a+b+c) ≥ b*c*(b^2+c^2) + c*a*(c^2+a^2) + a*b*(a^2+b^2) := by
  intros
  grind
