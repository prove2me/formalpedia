-- Prove2me | solution 1 for mme_released_joint_zero_size_profile
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:51.463462+00:00
-- url     : https://prove2.me/submissions/c7b26b73-6aa4-440f-ad6e-1365356c2220

import Definitions.Def_mme_released_joint_interior_profiles
import Mathlib.Tactic

open MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed

/-- A parent label with zero physical size has no child occurrences in any mode. -/
theorem solution (r : Fin 6) (k : ℕ) (j : Fin 270)
    (hj : size r k j = 0) (i : Fin 3)
    (c : MME.RecursiveThinSplit.Split 4 (parent r j))
    (w : MME.CompleteSplit.CompleteWord 2) :
    integerProfile r k i ⟨j, c⟩ w = 0 := by
  simp only [size, MME.ReleasedInterior.regionalSize, Nat.mul_eq_zero] at hj
  norm_num [denominator] at hj
  rcases hj with (hk | hw) | hr
  · simp [integerProfile, hk]
  · simp [integerProfile, hw]
  · simp [integerProfile, MME.ReleasedInterior.integerProfile, hr]


#print axioms solution
