-- Prove2me | solution 1 for lean_workbook_plus_43239
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:15.855761+00:00
-- url     : https://prove2.me/submissions/86532f0b-3a7d-49b6-aacc-61431f4ea65c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) (h : x*y*z = 1) :
  x^6 + y^6 + z^6 ≥ x*y*z*(x^3 + y^3 + z^3) := by
  intros
  
  have h_identity : (x^6 + y^6 + z^6) - (x*y*z*(x^3 + y^3 + z^3)) = ((3 / 4) : ℝ) * 1 * (((z * (x ^ 2)) + ((-1) * z * (y ^ 2))))^2 + ((1 / 4) : ℝ) * 1 * ((((-1) * (z ^ 3)) + (z * (x ^ 2))))^2 + ((1 / 2) : ℝ) * 1 * (((x ^ 3) + ((-1) * x * y * z)))^2 + ((1 / 2) : ℝ) * 1 * (((x ^ 3) + ((-1) * x * (z ^ 2))))^2 + ((1 / 2) : ℝ) * 1 * ((((-1) * (y ^ 3)) + (x * y * z)))^2 + ((1 / 2) : ℝ) * 1 * ((((-1) * (z ^ 3)) + (x * y * z)))^2 + ((1 / 4) : ℝ) * 1 * ((((-1) * (z ^ 3)) + (z * (y ^ 2))))^2 + ((1 / 2) : ℝ) * 1 * (((y ^ 3) + ((-1) * y * (z ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (x^6 + y^6 + z^6) - (x*y*z*(x^3 + y^3 + z^3)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
