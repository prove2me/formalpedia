-- Prove2me | solution 1 for mme_released_global_joint_recursive_continuation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-22T21:23:38.744751+00:00
-- url     : https://prove2.me/submissions/33e3483a-b113-464c-b047-7bf48978f161
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_mme_released_global_joint_interface
import Theorems.Thm_mme_released_global_joint_recursive_continuation_fixed_caps_v3

open BigOperators MME MME.TensorObj MME.ProfiledCW MME.GlobalCW
  MME.RegionRealization MME.ReleasedGlobal
set_option autoImplicit false
universe u

theorem solution :
    Exists (fun eta : Fin 6 -> Real =>
      ((o : Fin 6) -> 0 < eta o) /\
      ((eps : Fin 6 -> Real) -> ((o : Fin 6) -> 0 < eps o) ->
        ((o : Fin 6) -> eps o <= eta o) ->
          (k0 : Nat) -> Exists (fun k : Nat => k0 <= k /\
            ((hk : 0 < k^2) -> (a : (o : Fin 6) -> Reference o (k^2)) ->
              Exists (fun R : LogJointRecipe (4 * (6 * blocks (k^2))) 3
                  (jointWindow (k^2) hk a eps) =>
                1 <= R.inputs /\ 1 <= R.a * R.b * R.c /\
                (6 * blocks (k^2) : Nat) * ((1322355 : Real)/1000000) +
                    Real.log (R.inputs : Real) <= R.logOutputs /\
                (6 * blocks (k^2) : Nat) *
                    (3 * ((209612367517 : Real)/100000000000) - 1/10000000) <=
                      Real.log ((R.a * R.b * R.c : Nat) : Real)))))) := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro o
    norm_num
  · intro eps heps hle k0
    exact mme_released_global_joint_recursive_continuation_fixed_caps_v3
      eps heps (fun o => by simpa using hle o) k0
