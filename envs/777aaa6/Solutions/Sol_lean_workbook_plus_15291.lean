-- Prove2me | solution 1 for lean_workbook_plus_15291
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:05:58.819551+00:00
-- url     : https://prove2.me/submissions/34e58465-1cb7-4fc3-89d9-38999e8aec9d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ n : ℕ, 2 ≤ n → 5 ^ n + 9 < 6 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ, pow_succ]
    omega
