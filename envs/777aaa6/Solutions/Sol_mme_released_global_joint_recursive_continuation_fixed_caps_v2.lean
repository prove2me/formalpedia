-- Prove2me | solution 1 for mme_released_global_joint_recursive_continuation_fixed_caps_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-22T22:08:43.651976+00:00
-- url     : https://prove2.me/submissions/cb86a57a-5a38-481b-ae92-6c3a5d05684b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_released_global_joint_recursive_continuation_fixed_caps_v3

open BigOperators MME MME.TensorObj MME.ProfiledCW MME.GlobalCW MME.RegionRealization MME.ReleasedGlobal
set_option autoImplicit false
universe u

theorem solution :
    (eps : Fin 6 → Real) → ((o : Fin 6) → 0 < eps o) →
      ((o : Fin 6) → eps o ≤ 1) → (k0 : Nat) →
        Exists (fun k : Nat => k0 ≤ k ∧
          ((hk : 0 < k^2) → (a : (o : Fin 6) → Reference o (k^2)) →
            Exists (fun R : LogJointRecipe (4 * (6 * blocks (k^2))) 3
                (jointWindow (k^2) hk a eps) =>
              1 ≤ R.inputs ∧ 1 ≤ R.a * R.b * R.c ∧
              (6 * blocks (k^2) : Real) * ((1322355 : Real)/1000000) +
                Real.log (R.inputs : Real) ≤ R.logOutputs ∧
              (6 * blocks (k^2) : Real) *
                  (3 * ((209612367517 : Real)/100000000000) - 1/10000000) ≤
                Real.log ((R.a * R.b * R.c : Nat) : Real)))) := by
  intro eps heps hcaps k0
  simpa only [Nat.cast_mul] using
    (mme_released_global_joint_recursive_continuation_fixed_caps_v3
      eps heps hcaps k0)
