-- Prove2me | solution 1 for lean_workbook_plus_46033
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:02.892698+00:00
-- url     : https://prove2.me/submissions/1f458842-10fe-4713-8834-70dc60daa9ad

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ)
  (h₀ : 5 ≤ n) :
  (2^n) > n^2 := by
  induction n,h₀ using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    nlinarith [sq_nonneg (n-1),Nat.mul_le_mul_left n (show 5≤n from hn)]
