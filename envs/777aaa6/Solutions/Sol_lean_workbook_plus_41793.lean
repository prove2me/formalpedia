-- Prove2me | solution 1 for lean_workbook_plus_41793
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:59.300564+00:00
-- url     : https://prove2.me/submissions/480020c3-b3d6-47ac-a051-e845df651b1c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a ≤ b ∧ b ≤ c) :
  a * b * (a + b) + b * c * (b + c) + c * a * (c + a) ≤ 2 * (a^3 + b^3 + c^3) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
