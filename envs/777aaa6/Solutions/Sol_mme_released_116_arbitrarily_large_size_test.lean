-- Prove2me | solution 1 for mme_released_116_arbitrarily_large_size_test
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T13:34:28.560167+00:00
-- url     : https://prove2.me/submissions/d4c85234-fc1b-49eb-b0ce-acb37221ab92

import Definitions.Def_mme_released_116_integer_profiles
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.NormNum

open BigOperators MME MME.Released116 MME.MoreAsymmetryExactSeed
set_option autoImplicit false

/-- The released integer counts share the denominator-square divisor,
and every region is at least that large. -/
theorem mme_released_116_integer_divisibility :
    (∀ r : Fin 6, denominator ^ 2 ≤ regionalSize r) ∧
      ∀ (r : Fin 6) (c : Split), denominator ^ 2 ∣ splitCount r c := by
  constructor
  · decide +kernel
  · intro r c
    exact dvd_mul_left _ _

/-- Positive replication preserves the common divisor and the regional lower bound. -/
theorem mme_released_116_scaled_integer_divisibility (k : ℕ) (hk : 0 < k) :
    0 < k * denominator ^ 2 ∧
      (∀ r : Fin 6, k * denominator ^ 2 ≤ k * regionalSize r) ∧
      ∀ (r : Fin 6) (c : Split), k * denominator ^ 2 ∣ k * splitCount r c := by
  refine ⟨Nat.mul_pos hk (by norm_num [denominator]), ?_, ?_⟩
  · intro r
    exact Nat.mul_le_mul_left k (mme_released_116_integer_divisibility.1 r)
  · intro r c
    exact Nat.mul_dvd_mul_left k (mme_released_116_integer_divisibility.2 r c)

/-- Every positive tolerance admits arbitrarily large integer scales satisfying
the extraction size test with repair scale two and the denominator-square minimum. -/
theorem solution
    (eps : ℝ) (heps : 0 < eps) (K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ 0 < k ∧
      (8 * 2 : ℝ) * (25 * 6 *
        (Fintype.card (CompleteSplit.CompleteWord 2) : ℝ) ^ 2) ≤
        (k * denominator ^ 2 : ℕ) * eps ^ 2 := by
  let B : ℝ := (8 * 2 : ℝ) * (25 * 6 *
    (Fintype.card (CompleteSplit.CompleteWord 2) : ℝ) ^ 2)
  have hfactor : 0 < (denominator : ℝ) ^ 2 * eps ^ 2 := by
    exact mul_pos (by norm_num [denominator]) (sq_pos_of_pos heps)
  obtain ⟨j, hj⟩ := exists_nat_gt (B / ((denominator : ℝ) ^ 2 * eps ^ 2))
  let k := max K (j + 1)
  have hjk : j < k := lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right _ _)
  have hkr : (j : ℝ) < k := by exact_mod_cast hjk
  have hB : B < (k : ℝ) * ((denominator : ℝ) ^ 2 * eps ^ 2) :=
    (div_lt_iff₀ hfactor).mp (hj.trans hkr)
  refine ⟨k, le_max_left _ _, lt_of_le_of_lt (Nat.zero_le j) hjk, ?_⟩
  simpa only [B, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hB.le

#print axioms solution
