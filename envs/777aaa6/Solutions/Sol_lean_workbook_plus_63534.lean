-- Prove2me | solution 1 for lean_workbook_plus_63534
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:30:25.21793+00:00
-- url     : https://prove2.me/submissions/75d66038-9c4b-443a-b4d5-adb30aaea52a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 2 * (a^3 + b^3 + c^3) < (a + b + c) * (a^2 + b^2 + c^2) ∧ (a + b + c) * (a^2 + b^2 + c^2) ≤ 3 * (a^3 + b^3 + c^3) := by
  constructor
  · have h1 := mul_pos (sq_pos_of_pos hx.1) (show 0 < b+c-a by linarith)
    have h2 := mul_pos (sq_pos_of_pos hx.2.1) (show 0 < a+c-b by linarith)
    have h3 := mul_pos (sq_pos_of_pos hx.2.2) (show 0 < a+b-c by linarith)
    nlinarith
  · have h1 := mul_nonneg (sq_nonneg (a-b)) (show 0 ≤ a+b by linarith [hx.1,hx.2.1])
    have h2 := mul_nonneg (sq_nonneg (b-c)) (show 0 ≤ b+c by linarith [hx.2.1,hx.2.2])
    have h3 := mul_nonneg (sq_nonneg (c-a)) (show 0 ≤ c+a by linarith [hx.2.2,hx.1])
    nlinarith
