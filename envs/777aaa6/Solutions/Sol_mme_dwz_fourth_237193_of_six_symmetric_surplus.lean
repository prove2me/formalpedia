-- Prove2me | solution 1 for mme_dwz_fourth_237193_of_six_symmetric_surplus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T16:06:23.858699+00:00
-- url     : https://prove2.me/submissions/ac004622-f8f6-4d15-9ae9-35e8d44ae1cb

import Theorems.Thm_mme_CW_fourth_asymptoticRank_le
import Theorems.Thm_mme_CW_fourth_six_symmetrization_iso
import Theorems.Thm_mme_six_symmetric_tau_value_to_direct_of_iso
import Theorems.Thm_mme_strassen_lt_three_mul_of_tau_value_surplus
import Theorems.Thm_mme_omega_eq_strassen

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (hsurplus : ∃ V : ℝ, (2401 : ℝ) < V ∧
      HasSixSymmetricTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 5) (790643 / 1000000) V) :
    matMulExp K < 237193 / 100000 := by
  obtain ⟨V, hV, hvalue⟩ := hsurplus
  have hnonneg : 0 ≤ V := by linarith
  have hdirect : HasTauValueAtLeast
      (MME.StothersFourth.cwFourthObj K 5) (790643 / 1000000) V :=
    mme_six_symmetric_tau_value_to_direct_of_iso
      (MME.StothersFourth.cwFourthObj K 5) (790643 / 1000000) V hnonneg
      (mme_CW_fourth_six_symmetrization_iso 5) hvalue
  have hrank : tensorAsymptoticRank (MME.StothersFourth.cwFourthObj K 5) ≤
      (2401 : ℝ) := by
    have h := mme_CW_fourth_asymptoticRank_le (K := K) 5
    norm_num at h
    exact h
  have hexponent : matMulExp_strassen K < 3 * (790643 / 1000000 : ℝ) :=
    mme_strassen_lt_three_mul_of_tau_value_surplus
      (K := K) (T := MME.StothersFourth.cwFourthObj K 5)
      (tau := (790643 / 1000000 : ℝ)) (V := V) (R := (2401 : ℝ))
      (by norm_num) (by linarith) (by norm_num) hrank hdirect hV
  rw [mme_omega_eq_strassen]
  exact hexponent.trans (by norm_num)
