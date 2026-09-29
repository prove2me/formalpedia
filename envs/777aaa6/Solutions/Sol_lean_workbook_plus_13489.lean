-- Prove2me | solution 1 for lean_workbook_plus_13489
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:43:22.026119+00:00
-- url     : https://prove2.me/submissions/71f9b83d-a21b-43b3-b905-e2b44b2b61e0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) (hn : 2 ≤ n) : (a + b) ^ n > a ^ n + b ^ n := by
  induction n, hn using Nat.le_induction with
  | base => nlinarith only [mul_pos ha hb]
  | succ k hk ih =>
    rw [pow_succ, pow_succ, pow_succ]
    have h := mul_lt_mul_of_pos_right ih (add_pos ha hb)
    nlinarith only [h, mul_pos (pow_pos ha k) hb, mul_pos (pow_pos hb k) ha]
