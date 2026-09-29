-- Prove2me | solution 1 for lean_workbook_plus_55030
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:14.555265+00:00
-- url     : https://prove2.me/submissions/8df35cc2-5696-4b53-9d58-0d42c2b53d2d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x y : ℝ, 3 * (x ^ 2 + x * y + y ^ 2) ≥ (9 / 4) * (x + y) ^ 2 := by
  intro x y
  intros
  have h : (0 : ℝ) ≤ (3 * (x ^ 2 + x * y + y ^ 2)) - ((9 / 4) * (x + y) ^ 2) := by
    calc
      0 ≤ ((3 / 4) : ℝ) * ((y + ((-1) * x)))^2 := by positivity
      _ = (3 * (x ^ 2 + x * y + y ^ 2)) - ((9 / 4) * (x + y) ^ 2) := by ring
  exact sub_nonneg.mp h
