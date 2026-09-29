-- Prove2me | solution 1 for lean_workbook_plus_14755
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:15:04.296858+00:00
-- url     : https://prove2.me/submissions/59751402-eeca-4267-beb5-6ffcca0203df

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : 3 * ((a / (a + 2 * b)) ^ 2 + (b / (b + 2 * c)) ^ 2 + (c / (c + 2 * a)) ^ 2) ≥ (a / (a + 2 * b) + b / (b + 2 * c) + c / (c + 2 * a)) ^ 2 := by
  have hCS (u v w : ℝ) : (u+v+w)^2 ≤ 3*(u^2+v^2+w^2) := by
    nlinarith [sq_nonneg (u-v), sq_nonneg (u-w), sq_nonneg (v-w)]
  exact hCS (a/(a+2*b)) (b/(b+2*c)) (c/(c+2*a))
