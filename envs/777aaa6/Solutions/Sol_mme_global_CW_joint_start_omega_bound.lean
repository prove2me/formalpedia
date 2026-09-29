-- Prove2me | solution 1 for mme_global_CW_joint_start_omega_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T07:29:45.973166+00:00
-- url     : https://prove2.me/submissions/35f4ed71-6680-49ad-a2be-c66fb80bd913

import Theorems.Thm_mme_global_CW_joint_start_sound
import Theorems.Thm_mme_CW_copied_finite_surplus_omega_bound
open MME MME.TensorObj MME.GlobalCW
set_option autoImplicit false
universe u

theorem solution {K : Type u} [Field K] {M ell : ℕ} (D : GlobalCW.Start M ell)
    (tau : ℝ) (hvolume : 1 ≤ D.a * D.b * D.c)
    (hsurplus : ((D.inputs * 7 ^ M : ℕ) : ℝ) <
      Real.exp D.logOutputs * (((D.a * D.b * D.c : ℕ) : ℝ) ^ tau)) :
    matMulExp K < 3 * tau := by
  obtain ⟨outputs,houtputs,hextract⟩ := mme_global_CW_joint_start_sound (K := K) D
  apply mme_CW_copied_finite_surplus_omega_bound M D.inputs outputs D.a D.b D.c tau
    hvolume hextract
  exact hsurplus.trans_le (mul_le_mul_of_nonneg_right houtputs (Real.rpow_nonneg (by positivity) _))
