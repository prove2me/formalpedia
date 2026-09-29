-- Prove2me | solution 1 for lean_workbook_plus_63713
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:13.369125+00:00
-- url     : https://prove2.me/submissions/baaeb461-06f1-4272-b8e4-9534636335ff

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) (hn : 2 ≤ n) : 5^n + 9 < 6^n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ,pow_succ]
    omega
