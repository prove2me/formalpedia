-- Prove2me | solution 1 for lean_workbook_plus_31571
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:29:33.547203+00:00
-- url     : https://prove2.me/submissions/6797a615-20ee-40e1-a51a-8b754ac86816

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℕ) (hx: x ≥ 3) : 3^x > x^2 + 3*x + 1 := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
    have hp : (x+1)^2+3*(x+1)+1 ≤ 3*(x^2+3*x+1) := by
      ring_nf
      omega
    have hm := Nat.mul_lt_mul_of_pos_left ih (by decide : 0 < 3)
    rw [pow_succ]
    omega
