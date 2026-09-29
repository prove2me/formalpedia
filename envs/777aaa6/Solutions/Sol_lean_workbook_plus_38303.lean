-- Prove2me | solution 1 for lean_workbook_plus_38303
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:20:15.765223+00:00
-- url     : https://prove2.me/submissions/c15fd6cf-c5eb-493c-8349-ad1619413fd6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (p q : ℚ) (r : ℝ) (hr : r = p + q * Real.sqrt 7) : ∃ a b c d : ℤ, a * d - b * c = 1 ∧ (a * r + b) / (c * r + d) = r   := by
  refine ⟨1, 0, 0, 1, ?_, ?_⟩ <;> norm_num
