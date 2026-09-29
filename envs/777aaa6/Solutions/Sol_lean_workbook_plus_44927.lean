-- Prove2me | solution 1 for lean_workbook_plus_44927
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:58:24.811468+00:00
-- url     : https://prove2.me/submissions/0729ffa4-2f2a-4878-9891-00db4d1de9b9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) :
  (a^2 * b + b^2 * c + c^2 * a)^2 ≤ (a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) := by
  nlinarith [sq_nonneg (a*(b*c)-b*(a*b)), sq_nonneg (a*(c*a)-c*(a*b)), sq_nonneg (b*(c*a)-c*(b*c))]
