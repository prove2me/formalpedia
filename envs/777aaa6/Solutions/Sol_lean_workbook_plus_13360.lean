-- Prove2me | solution 1 for lean_workbook_plus_13360
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:00:08.796135+00:00
-- url     : https://prove2.me/submissions/584ccb63-ba1e-4158-8d22-9753c4a54e92

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y : ℕ → ℕ) (hx : x 0 = 3) (hy : y 0 = 2) (hn: ∀ n, x (n + 1) = 3 * x n + 4 * y n) (h'n: ∀ n, y (n + 1) = 2 * x n + 3 * y n) : ∀ n, (x n)^2 - 2 * (y n)^2 = 1 := by
  have he : ∀ n, (x n)^2=2*(y n)^2+1 := by
    intro n
    induction n with
    | zero => rw [hx,hy]; norm_num
    | succ n ih =>
      rw [hn,h'n]
      nlinarith only [ih]
  intro n
  have hh := he n
  omega
