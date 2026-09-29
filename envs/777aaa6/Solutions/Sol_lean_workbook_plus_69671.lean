-- Prove2me | solution 1 for lean_workbook_plus_69671
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:37.92731+00:00
-- url     : https://prove2.me/submissions/7bc7da4a-0a26-447e-8fc6-e2728b8e37ff

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) : x^4 + y^4 + z^4 + (x*y + y*z + z*x)*(x^2 + y^2 + z^2) ≥ 4*x*y*z*(x + y + z) := by
  intros
  
  have h_identity : (x^4 + y^4 + z^4 + (x*y + y*z + z*x)*(x^2 + y^2 + z^2)) - (4*x*y*z*(x + y + z)) = (1 : ℝ) * 1 * (((x ^ 2) + ((-1 / 2) * (y ^ 2)) + ((-1 / 2) * (z ^ 2)) + ((1 / 2) * x * y) + ((1 / 2) * x * z) + ((-1) * y * z)))^2 + ((3 / 4) : ℝ) * 1 * (((y ^ 2) + ((-1) * (z ^ 2)) + (x * y) + ((-1) * x * z)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (x^4 + y^4 + z^4 + (x*y + y*z + z*x)*(x^2 + y^2 + z^2)) - (4*x*y*z*(x + y + z)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
