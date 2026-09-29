-- Prove2me | solution 1 for lean_workbook_plus_27046
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:58.353569+00:00
-- url     : https://prove2.me/submissions/d56e2cf3-dfff-4db0-b351-e41a61ef4d99

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / a + 3 / (a + b) ≤ 4 / 3 * (1 / a + 1 / b) := by
  have hi : 4/3*(1/a+1/b)-(1/a+3/(a+b)) = (2*a-b)^2/(3*a*b*(a+b)) := by
    field_simp
    ring
  have hp : 0 ≤ (2*a-b)^2/(3*a*b*(a+b)) := by positivity
  linarith
