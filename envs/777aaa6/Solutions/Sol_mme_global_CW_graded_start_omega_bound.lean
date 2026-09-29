-- Prove2me | solution 1 for mme_global_CW_graded_start_omega_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T15:54:10.368641+00:00
-- url     : https://prove2.me/submissions/612f0ca1-3147-40ea-a9db-cebdff84ecd2

import Theorems.Thm_mme_global_CW_graded_start_sound
import Theorems.Thm_mme_CW_copied_finite_surplus_omega_bound
import Definitions.Def_mme_omega

open MME MME.TensorObj MME.GlobalCW
set_option autoImplicit false
universe u

theorem solution {K : Type u} [Field K] {M ell : ℕ} (D : GlobalCW.StartG M ell)
    (tau : ℝ) (hvolume : 1 ≤ D.a * D.b * D.c)
    (hsurplus : ((D.inputs * 7 ^ M : ℕ) : ℝ) <
      Real.exp D.logOutputs * (((D.a * D.b * D.c : ℕ) : ℝ) ^ tau)) :
    matMulExp K < 3 * tau := by
  obtain ⟨outputs,houtputs,hextract⟩ := mme_global_CW_graded_start_sound (K := K) D
  apply mme_CW_copied_finite_surplus_omega_bound M D.inputs outputs D.a D.b D.c tau
    hvolume hextract
  exact hsurplus.trans_le (mul_le_mul_of_nonneg_right houtputs (Real.rpow_nonneg (by positivity) _))
