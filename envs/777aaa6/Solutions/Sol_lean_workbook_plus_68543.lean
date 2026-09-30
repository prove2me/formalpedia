-- Prove2me | solution 1 for lean_workbook_plus_68543
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:14:07.029482+00:00
-- url     : https://prove2.me/submissions/08d46560-7a89-42ea-9f61-58cd71405a40

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : a + b + c = 0) (hb : a ^ 2 + b ^ 2 + c ^ 2 = 0) (hc : a ^ 3 + b ^ 3 + c ^ 3 = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have h1 : a ^ 2 = 0 := by linarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have h2 : b ^ 2 = 0 := by linarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have h3 : c ^ 2 = 0 := by linarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  exact ⟨pow_eq_zero_iff two_ne_zero |>.mp h1, pow_eq_zero_iff two_ne_zero |>.mp h2,
    pow_eq_zero_iff two_ne_zero |>.mp h3⟩
