-- Prove2me | solution 1 for lean_workbook_plus_45770
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:55:07.471261+00:00
-- url     : https://prove2.me/submissions/2aa706a9-6391-4886-898e-2a1793f6bad6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (h₁ : 0 < y ∧ y ≤ x ∧ x ≤ 2) (h₂ : x * y ^ 2 ≤ 2) : x + 2 * y ≤ 4 := by
  intros
  nlinarith [sq_nonneg (2*x-y), sq_nonneg (x-2*y), sq_nonneg (x+y)]
