-- Prove2me | solution 1 for lean_workbook_plus_26101
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:37.684799+00:00
-- url     : https://prove2.me/submissions/064fe71b-2656-4a4d-8e9f-4c2de6889f0f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x₂ x₃ : ℝ) :
  Real.sqrt (x₂^2 + (1 - x₃)^2) ≥ (Real.sqrt 2 / 2) * (x₂ + 1 - x₃) := by
  apply Real.le_sqrt_of_sq_le
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have he : (Real.sqrt 2/2*(x₂+1-x₃))^2=(x₂+1-x₃)^2/2 := by rw [mul_pow,div_pow,hs]; ring
  rw [he]
  nlinarith only [sq_nonneg (x₂-(1-x₃))]
