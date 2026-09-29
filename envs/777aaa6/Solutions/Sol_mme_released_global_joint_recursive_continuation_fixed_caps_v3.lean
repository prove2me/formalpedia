-- Prove2me | solution 1 for mme_released_global_joint_recursive_continuation_fixed_caps_v3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-22T21:42:44.26668+00:00
-- url     : https://prove2.me/submissions/451068f1-e44a-4e43-b57d-588b554055c9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_released_global_joint_recursive_continuation_fixed_caps_v2

open BigOperators MME MME.TensorObj MME.ProfiledCW MME.GlobalCW MME.RegionRealization MME.ReleasedGlobal
set_option autoImplicit false
universe u

theorem solution :
    (eps : Fin 6 → Real) → (∀ o, 0 < eps o) → (∀ o, eps o ≤ 1) → (k0 : Nat) →
      ∃ k : Nat, k0 ≤ k ∧
        ∀ (hk : 0 < k^2) (a : ∀ o : Fin 6, Reference o (k^2)),
          ∃ R : LogJointRecipe (4 * (6 * blocks (k^2))) 3 (jointWindow (k^2) hk a eps),
            1 ≤ R.inputs ∧ 1 ≤ R.a * R.b * R.c ∧
              (6 * blocks (k^2) : Nat) * ((1322355 : Real) / 1000000) +
                Real.log (R.inputs : Real) ≤ R.logOutputs ∧
              (6 * blocks (k^2) : Nat) *
                (3 * ((209612367517 : Real) / 100000000000) - 1 / 10000000) ≤
                  Real.log ((R.a * R.b * R.c : Nat) : Real) := by
  intro eps heps hcaps k0
  simpa only [Nat.cast_mul] using
    (mme_released_global_joint_recursive_continuation_fixed_caps_v2
      eps heps hcaps k0)
