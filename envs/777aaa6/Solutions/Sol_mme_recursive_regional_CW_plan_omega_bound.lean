-- Prove2me | solution 1 for mme_recursive_regional_CW_plan_omega_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T15:31:49.700146+00:00
-- url     : https://prove2.me/submissions/b0aff37a-6e9b-4af5-8bf0-06682cc88d95

import Theorems.Thm_mme_recursive_regional_CW_plan_sound
import Theorems.Thm_mme_CW_copied_finite_surplus_omega_bound
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME MME.TensorObj MME.ProfiledCW
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u

theorem solution {K : Type u} [Field K] {N ell : ℕ} {P : Predicate N}
    (D : RegionalPlan N ell P) (tau : ℝ)
    (hvolume : 1 ≤ D.a * D.b * D.c)
    (hsurplus : ((D.inputs * 7 ^ N : ℕ) : ℝ) <
      (D.outputs : ℝ) * (((D.a * D.b * D.c : ℕ) : ℝ) ^ tau)) :
    matMulExp K < 3 * tau := by
  have hp : Restrict (tensor K P) (raw K N) :=
    ⟨fun i ↦ ((raw K N).basisAllAllowedGrading (canonical K N)
      (fun i x ↦ P i (fine x))).blockProj i 0, rfl⟩
  exact mme_CW_copied_finite_surplus_omega_bound N D.inputs D.outputs D.a D.b D.c tau hvolume
    ((mme_recursive_regional_CW_plan_sound D).trans
      (mme_bigAdd_mono_restrict (fun _ : Fin D.inputs ↦ hp))) hsurplus
