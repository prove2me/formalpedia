-- Prove2me | solution 1 for double_factorial_central_quotient_le_two_p_pow
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-24T15:52:38.50155+00:00
-- url     : https://prove2.me/submissions/eda30d1a-fbae-4a8f-a152-7e9f78173ea0

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

theorem solution (p : ℕ) :
    ((Nat.factorial (2 * p) : ℝ) / ((2 ^ p : ℝ) * (Nat.factorial p : ℝ))) ≤ (2 * p : ℝ) ^ p := by
  induction p with
  | zero => simp
  | succ n ih =>
    -- recurrence: dfR (n+1) = dfR n * (2n+1)
    have hrec : ((Nat.factorial (2 * (n + 1)) : ℝ) / ((2 ^ (n + 1) : ℝ) * (Nat.factorial (n + 1) : ℝ)))
        = ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) * (2 * n + 1) := by
      have h2 : (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
      have hfp : ((Nat.factorial (n + 1) : ℝ)) = (Nat.factorial n) * (n + 1) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have h2p : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
      have hf2 : ((Nat.factorial (2 * (n + 1)) : ℝ)) =
          (Nat.factorial (2 * n) : ℝ) * (2 * n + 1) * (2 * n + 2) := by
        rw [h2p, Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        ring
      rw [h2, hfp, hf2]
      have hpfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
      field_simp
    rw [hrec]
    have hbase : (0 : ℝ) ≤ (2 * n : ℝ) := by positivity
    rw [show (2 * (↑(n + 1) : ℝ)) = 2 * (n : ℝ) + 2 by push_cast; ring, pow_succ]
    have hmono : (2 * n : ℝ) ^ n ≤ (2 * n + 2 : ℝ) ^ n :=
      pow_le_pow_left₀ hbase (by linarith) n
    calc ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) * (2 * n + 1)
        ≤ (2 * n : ℝ) ^ n * (2 * n + 1) := by
          apply mul_le_mul_of_nonneg_right ih; positivity
      _ ≤ (2 * n + 2 : ℝ) ^ n * (2 * n + 2) := by
          apply mul_le_mul hmono (by linarith) (by linarith) (by positivity)

#print axioms solution
