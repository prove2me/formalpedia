-- Prove2me | solution 1 for mme_released_global_graded_joint_recursive_continuation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-22T21:43:31.296164+00:00
-- url     : https://prove2.me/submissions/0025eedf-3f77-4d72-b448-52f0275a02e6

import Theorems.Thm_mme_released_global_graded_joint_recursive_construction

open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RegionRealization MME.ReleasedGlobal
set_option autoImplicit false

theorem solution :
    ∃ eta : Fin 6 → ℝ, (∀ o, 0 < eta o) ∧
      ∀ eps : Fin 6 → ℝ, (∀ o, 0 < eps o) → (∀ o, eps o ≤ eta o) →
        ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
          ∀ (hk : 0 < k^2) (a : ∀ o : Fin 6, Reference o (k^2)),
            ∃ R : LogJointRecipeG (4 * (6 * blocks (k^2))) 3 (jointWindow (k^2) hk a eps),
              1 ≤ R.inputs ∧ 1 ≤ R.a * R.b * R.c ∧
              ((6 * blocks (k^2) : ℕ) : ℝ) * ((13223546 : ℝ)/10000000) +
                Real.log (R.inputs : ℝ) ≤ R.logOutputs ∧
              ((6 * blocks (k^2) : ℕ) : ℝ) *
                (3 * ((209612367517 : ℝ)/100000000000) - 1/10000000) ≤
                  Real.log ((R.a * R.b * R.c : ℕ) : ℝ) := by
  simpa [Nat.cast_mul] using mme_released_global_graded_joint_recursive_construction
