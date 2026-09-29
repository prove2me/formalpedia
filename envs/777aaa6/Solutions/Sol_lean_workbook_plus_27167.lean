-- Prove2me | solution 1 for lean_workbook_plus_27167
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:06:56.924472+00:00
-- url     : https://prove2.me/submissions/887703b2-e209-4dab-aff8-a70b932f79eb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b c d : ℝ, a^4+b^4+c^4+d^4 ≥ a^2*b*c + b^2*c*d + c^2*d*a + d^2*a*b := by
  intro a b c d
  nlinarith only [sq_nonneg (a^2-b*c),sq_nonneg (b^2-c*d),sq_nonneg (c^2-d*a),sq_nonneg (d^2-a*b),sq_nonneg (a^2-b^2),sq_nonneg (b^2-c^2),sq_nonneg (c^2-d^2),sq_nonneg (d^2-a^2)]
