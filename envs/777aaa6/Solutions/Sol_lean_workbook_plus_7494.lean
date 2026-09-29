-- Prove2me | solution 1 for lean_workbook_plus_7494
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:23.827143+00:00
-- url     : https://prove2.me/submissions/2a6a4f42-575b-491f-8770-c91810153b69

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (h : (a + b) * (a + 4 * b) = 9) : a * b ≤ 1 := by
  intros
  nlinarith [sq_nonneg (2*a-b), sq_nonneg (a-2*b), sq_nonneg (a+b)]
