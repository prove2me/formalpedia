-- Prove2me | solution 1 for lean_workbook_plus_54848
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:49:34.346748+00:00
-- url     : https://prove2.me/submissions/101f8c23-7969-46c7-820f-d3b954f61f26

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a b c : ℝ} : a ^ 4 + b ^ 4 + c ^ 4 ≥ a * b * c * (a + b + c) := by
  have h₁ : a^4+b^4+c^4 ≥ a^2*b^2+b^2*c^2+c^2*a^2 := by
    nlinarith [sq_nonneg (a^2-b^2), sq_nonneg (b^2-c^2), sq_nonneg (c^2-a^2)]
  have h₂ : a^2*b^2+b^2*c^2+c^2*a^2 ≥ a*b*c*(a+b+c) := by
    nlinarith [sq_nonneg (a*b-b*c), sq_nonneg (b*c-c*a), sq_nonneg (c*a-a*b)]
  exact le_trans h₂ h₁
