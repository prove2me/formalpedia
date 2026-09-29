-- Prove2me | solution 1 for mme_joint_regional_CW_plan_omega_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T01:00:52.304092+00:00
-- url     : https://prove2.me/submissions/a63564db-2a0b-4a25-9be6-e0865f2696ef

import Definitions.Def_mme_joint_regional_CW_plan_data
import Definitions.Def_mme_omega
import Theorems.Thm_mme_joint_regional_CW_plan_sound
import Theorems.Thm_mme_CW_copied_finite_surplus_omega_bound
import Theorems.Thm_mme_bigAdd_mono_restrict
import Mathlib

open BigOperators MME MME.TensorObj MME.ProfiledCW
open scoped Classical

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

universe u

theorem solution {K : Type u} [Field K] {N ell : ℕ} {P : Predicate N}
    (D : JointPlan N ell P) (tau : ℝ)
    (hvolume : 1 ≤ D.a * D.b * D.c)
    (hsurplus : ((D.inputs * 7 ^ N : ℕ) : ℝ) <
      (D.outputs : ℝ) * (((D.a * D.b * D.c : ℕ) : ℝ) ^ tau)) :
    matMulExp K < 3 * tau := by
  have hp : TensorObj.Restrict (tensor K P) (raw K N) :=
    ⟨fun i ↦ ((raw K N).basisAllAllowedGrading (canonical K N)
      (fun i x ↦ P i (fine x))).blockProj i 0, rfl⟩
  exact mme_CW_copied_finite_surplus_omega_bound N D.inputs D.outputs D.a D.b D.c tau hvolume
    ((mme_joint_regional_CW_plan_sound D).trans
      (mme_bigAdd_mono_restrict (fun _ : Fin D.inputs ↦ hp))) hsurplus
