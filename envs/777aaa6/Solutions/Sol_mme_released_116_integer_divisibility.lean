-- Prove2me | solution 1 for mme_released_116_integer_divisibility
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T13:34:26.461601+00:00
-- url     : https://prove2.me/submissions/00628f4f-385c-4560-8e8d-518e08e30b21

import Definitions.Def_mme_released_116_integer_profiles
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.NormNum

open BigOperators MME MME.Released116 MME.MoreAsymmetryExactSeed
set_option autoImplicit false

/-- The released integer counts share the denominator-square divisor,
and every region is at least that large. -/
theorem solution :
    (∀ r : Fin 6, denominator ^ 2 ≤ regionalSize r) ∧
      ∀ (r : Fin 6) (c : Split), denominator ^ 2 ∣ splitCount r c := by
  constructor
  · decide +kernel
  · intro r c
    exact dvd_mul_left _ _

#print axioms solution
