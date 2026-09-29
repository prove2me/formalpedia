-- Prove2me | solution 1 for lean_workbook_plus_44317
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-09T01:31:59.042052+00:00
-- url     : https://prove2.me/submissions/3ad169c0-61e5-4f8b-b7f2-eea7efcbb505

import Theorems.Thm_lean_workbook_plus_44317
import Mathlib.Tactic.Linarith

theorem solution : ∀ a b : ℝ, (5*a^2 - 3*a*b + b^2)*(a - 3*b)^2 ≥ 0 := by
  intro a b
  nlinarith [mul_nonneg (sq_nonneg (10*a - 3*b)) (sq_nonneg (a - 3*b)),
             mul_nonneg (sq_nonneg b) (sq_nonneg (a - 3*b)), sq_nonneg (a - 3*b)]
