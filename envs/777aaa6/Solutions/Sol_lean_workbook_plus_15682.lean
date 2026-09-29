-- Prove2me | solution 1 for lean_workbook_plus_15682
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:59:55.438585+00:00
-- url     : https://prove2.me/submissions/61b2e714-38f5-4b29-85de-4b1d62734098

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (k : ℕ) (h₁ : 3 ≤ k) : 2 ^ (k + 1) > 4 * k + 1 := by
  induction k,h₁ using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    nlinarith
