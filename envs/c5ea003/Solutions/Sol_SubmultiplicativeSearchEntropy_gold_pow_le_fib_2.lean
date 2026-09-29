-- Prove2me | solution 2 for SubmultiplicativeSearchEntropy.gold_pow_le_fib
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T19:08:55.775682+00:00
-- url     : https://prove2.me/submissions/7ba80189-d789-49ea-bf0c-52eb4cc05d02

import Mathlib
import Definitions.Def_Bridges_SubmultiplicativeSearchEntropy
open SubmultiplicativeSearchEntropy in
theorem solution (n : ℕ) : Real.goldenRatio ^ n ≤ (Nat.fib (n + 3) : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Nat.fib_add_two]
  | one =>
    have h := Real.goldenRatio_lt_two
    norm_num [Nat.fib_add_two]
    linarith
  | more n ih1 ih2 =>
    -- `φ^{n+2} = φ^{n+1} + φⁿ` and Fibonacci satisfies the same recurrence
    have hφ : Real.goldenRatio ^ (n + 2) = Real.goldenRatio ^ (n + 1) + Real.goldenRatio ^ n := by
      have := Real.goldenRatio_pow_sub_goldenRatio_pow n
      linarith
    have hfib : (Nat.fib (n + 2 + 3) : ℝ) = Nat.fib (n + 1 + 3) + Nat.fib (n + 3) := by
      rw [show n + 2 + 3 = (n + 3) + 2 by ring, Nat.fib_add_two]
      push_cast
      ring_nf
    rw [hφ, hfib]
    linarith
