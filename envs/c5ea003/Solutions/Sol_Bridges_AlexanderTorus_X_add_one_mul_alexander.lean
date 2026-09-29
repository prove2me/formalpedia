-- Prove2me | solution 1 for Bridges.AlexanderTorus.X_add_one_mul_alexander
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T14:51:02.999822+00:00
-- url     : https://prove2.me/submissions/d586fb5a-4cb2-451a-8fad-e13b293b6a5d

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset

@[simp] lemma alexander_zero : alexander 0 = 0 := by simp [alexander]

lemma alexander_succ (N : ℕ) :
    alexander (N + 1) = alexander N + (-1) ^ N * X ^ N := by
  simp [alexander, Finset.sum_range_succ]

theorem solution (N : ℕ) :
    (X + 1) * alexander N = 1 - (-1) ^ N * X ^ N := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [alexander_succ, mul_add, ih, pow_succ (-1 : ℤ[X]) n, pow_succ X n]
      ring
