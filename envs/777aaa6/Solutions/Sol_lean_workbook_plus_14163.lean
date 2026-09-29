-- Prove2me | solution 1 for lean_workbook_plus_14163
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:20.091727+00:00
-- url     : https://prove2.me/submissions/eef574f8-51d5-49ba-9680-215c41134b2d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : a ≥ c ∧ c ≥ b) :
  (a - b) * (b - c) * (c - a) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
