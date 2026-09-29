-- Prove2me | solution 1 for lean_workbook_plus_21878
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:58:39.337195+00:00
-- url     : https://prove2.me/submissions/528f19dc-49b8-4fa1-a733-4dce1ee9fc07

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^3 + b^3 = 2) : a^2 + b^2 ≤ a^5 + b^5 ∧ a^5 + b^5 ≤ 2 * (a^2 + b^2) := by
  have he := congrArg (fun t:ℝ => t*(a^2+b^2)) hab
  have hA := mul_nonneg (mul_nonneg (sq_nonneg (a-b)) (add_nonneg ha hb)) (show 0≤a^2+a*b+b^2 by positivity)
  have hB : 0≤a^2*b^3+b^2*a^3 := by positivity
  constructor <;> nlinarith only [he,hA,hB]
