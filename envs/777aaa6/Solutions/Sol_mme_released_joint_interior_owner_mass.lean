-- Prove2me | solution 1 for mme_released_joint_interior_owner_mass
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T09:47:00.288079+00:00
-- url     : https://prove2.me/submissions/0ddda333-5e65-42b6-b90e-302c026d88bb

import Theorems.Thm_mme_released_interior_scaled_integer_profile_constraints_exact
import Definitions.Def_mme_released_joint_interior_frame

open scoped BigOperators
open MME MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed

/-- Regrouping the six inner regions restores the original owner-parent mass.
The equality also covers zero-weight and boundary labels. -/
theorem solution (k : ℕ) (j : Fin 270) :
    (∑ r : Fin 6, size r k j) = k * weight j * denominator ^ 4 := by
  by_cases hw : weight j = 0
  · simp [size, hw]
  · have hi : (ReleasedInterior.seed (component j).1 (component j).2).boundary = [] := by
      by_contra h
      exact hw (by simp only [weight, if_neg h])
    obtain ⟨a, ha, htotal, _⟩ :=
      mme_released_interior_scaled_integer_profile_constraints_exact
        (component j).1 (component j).2 hi 1 (by decide)
    have hs : (∑ r : Fin 6, ReleasedInterior.regionalSize
        (component j).1 (component j).2 r) = denominator ^ 4 := by
      simpa only [one_mul] using htotal
    simp only [size, ← Finset.mul_sum, hs]


#print axioms solution
