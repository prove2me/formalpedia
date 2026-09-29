-- Prove2me | solution 1 for lean_workbook_plus_31336
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:37:57.567995+00:00
-- url     : https://prove2.me/submissions/9c52a0ae-5cb2-4226-babe-4aeeae7baf6d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (k : ℕ) (h : 1 < k) : (3 : ℝ) ^ k > 2 ^ (k + 1) := by
  induction k, (show 2 ≤ k by omega) using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    calc
      (2:ℝ)^(k+1+1) = 2*2^(k+1) := by ring
      _ < 2*3^k := mul_lt_mul_of_pos_left (ih (by omega)) (by norm_num)
      _ < 3*3^k := by nlinarith [pow_pos (show (0:ℝ)<3 by norm_num) k]
      _ = 3^(k+1) := by ring
