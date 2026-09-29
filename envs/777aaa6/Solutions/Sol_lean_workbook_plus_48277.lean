-- Prove2me | solution 1 for lean_workbook_plus_48277
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:59:52.961567+00:00
-- url     : https://prove2.me/submissions/fd15d3a4-874d-44eb-bfff-618f5172d583

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (h : a^2 + b^2 + c^2 = a * b + b * c + c * a) : a = b ∧ b = c ∧ c = a := by
  have h1 : a=b := by nlinarith [sq_nonneg (a-b),sq_nonneg (b-c),sq_nonneg (c-a)]
  have h2 : b=c := by nlinarith [sq_nonneg (a-b),sq_nonneg (b-c),sq_nonneg (c-a)]
  exact ⟨h1,h2,h2.symm.trans h1.symm⟩
