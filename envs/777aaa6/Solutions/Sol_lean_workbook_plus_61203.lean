-- Prove2me | solution 1 for lean_workbook_plus_61203
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:29:25.004707+00:00
-- url     : https://prove2.me/submissions/f6d4a2ab-455b-40ce-94e3-776cd505d9ff

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) (h : n ≥ 3) : 4 ^ n ≥ (n + 1) ^ 3 := by
  induction n, h using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hsq : 1 ≤ n^2 := one_le_pow₀ (by omega : 1 ≤ n)
    have hp : (n+1+1)^3 ≤ 4*(n+1)^3 := by
      ring_nf
      omega
    have hm := Nat.mul_le_mul_left 4 ih
    rw [pow_succ]
    omega
