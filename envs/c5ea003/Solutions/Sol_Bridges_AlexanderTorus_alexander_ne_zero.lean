-- Prove2me | solution 1 for Bridges.AlexanderTorus.alexander_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T15:03:02.264381+00:00
-- url     : https://prove2.me/submissions/91908a5f-5c1b-41fd-8533-d9f64a41be5f

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

lemma X_add_one_mul_alexander_odd {N : ℕ} (hN : Odd N) :
    (X + 1) * alexander N = X ^ N + 1 := by
  rw [X_add_one_mul_alexander, hN.neg_one_pow]
  ring

theorem solution {N : ℕ} (hN : Odd N) : alexander N ≠ 0 := by
  intro h
  have hkey := X_add_one_mul_alexander_odd hN
  rw [h, mul_zero] at hkey
  have h0 := congrArg (Polynomial.eval 1) hkey
  simp at h0
