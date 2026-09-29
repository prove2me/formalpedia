-- Prove2me | solution 1 for lean_workbook_plus_31850
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:30:21.454328+00:00
-- url     : https://prove2.me/submissions/086560a7-08ff-47aa-b2ff-2e67ad2eb0a1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 3 * (a * b + b * c + c * a) ≤ (a + b + c) ^ 2 ∧ (a + b + c) ^ 2 < 4 * (a * b + b * c + c * a) := by
  constructor
  · nlinarith [sq_nonneg (a-b),sq_nonneg (b-c),sq_nonneg (c-a)]
  · have h1 := mul_pos hx.1 (show 0 < b+c-a by linarith)
    have h2 := mul_pos hx.2.1 (show 0 < a+c-b by linarith)
    have h3 := mul_pos hx.2.2 (show 0 < a+b-c by linarith)
    nlinarith
