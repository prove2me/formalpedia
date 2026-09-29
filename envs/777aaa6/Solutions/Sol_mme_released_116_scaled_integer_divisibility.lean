-- Prove2me | solution 1 for mme_released_116_scaled_integer_divisibility
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T13:34:27.627428+00:00
-- url     : https://prove2.me/submissions/dacdde10-3332-48ed-9199-eb6cfb57a9b1

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
theorem solution (k : ℕ) (hk : 0 < k) :
    0 < k * denominator ^ 2 ∧
      (∀ r : Fin 6, k * denominator ^ 2 ≤ k * regionalSize r) ∧
      ∀ (r : Fin 6) (c : Split), k * denominator ^ 2 ∣ k * splitCount r c := by
  refine ⟨Nat.mul_pos hk (by norm_num [denominator]), ?_, ?_⟩
  · intro r
    exact Nat.mul_le_mul_left k (mme_released_116_integer_divisibility.1 r)
  · intro r c
    exact Nat.mul_dvd_mul_left k (mme_released_116_integer_divisibility.2 r c)

#print axioms solution
