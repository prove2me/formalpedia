-- Prove2me | solution 1 for lean_workbook_plus_14564
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:09:53.770105+00:00
-- url     : https://prove2.me/submissions/d6a395f6-f27e-4253-931e-6b4aeccb309d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) (hn : 9 < n) (h : 2^n > n^3) : 2^(n + 1) > (n + 1)^3 := by
  have h2 : 10*n≤n^2 := by nlinarith [mul_nonneg (show (0:ℤ)≤n by positivity) (show (0:ℤ)≤(n:ℤ)-10 by omega)]
  have h3 : 10*n^2≤n^3 := by nlinarith [Nat.mul_le_mul_right (n^2) (show 10≤n by omega)]
  rw [pow_succ]
  nlinarith
