-- Prove2me | solution 1 for Bridges.AlexanderTorus.X_add_one_mul_alexander_odd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T14:58:40.547711+00:00
-- url     : https://prove2.me/submissions/0f6e48a3-ca87-4403-8f55-17322114ea07

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset

@[simp] lemma alexander_zero : alexander 0 = 0 := by simp [alexander]

lemma alexander_succ (N : ℕ) :
    alexander (N + 1) = alexander N + (-1) ^ N * X ^ N := by
  simp [alexander, Finset.sum_range_succ]

lemma X_add_one_mul_alexander (N : ℕ) :
    (X + 1) * alexander N = 1 - (-1) ^ N * X ^ N := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [alexander_succ, mul_add, ih, pow_succ (-1 : ℤ[X]) n, pow_succ X n]
      ring

theorem solution {N : ℕ} (hN : Odd N) :
    (X + 1) * alexander N = X ^ N + 1 := by
  rw [X_add_one_mul_alexander, hN.neg_one_pow]
  ring
