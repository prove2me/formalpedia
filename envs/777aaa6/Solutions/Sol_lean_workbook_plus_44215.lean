-- Prove2me | solution 1 for lean_workbook_plus_44215
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:42.470202+00:00
-- url     : https://prove2.me/submissions/b6440268-d1fd-4ede-98b9-5506b61ab447

import Mathlib
set_option autoImplicit false

theorem solution (a b c: ℝ) : a^2 + b^2 ≥ 2*a*b ∧ b^2 + c^2 ≥ 2*b*c ∧ c^2 + a^2 ≥ 2*c*a   := by
  exact ⟨by nlinarith [sq_nonneg (a - b)], by nlinarith [sq_nonneg (b - c)], by nlinarith [sq_nonneg (c - a)]⟩

#print axioms solution
