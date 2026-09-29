-- Prove2me | solution 1 for mme_omega_lt_23737
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T19:24:52.307208+00:00
-- url     : https://prove2.me/submissions/06c2c82a-47bd-4e9f-9e23-5ca03966b877

import Theorems.Thm_mme_stothers_fourth_fixed_tau_value_23737
import Theorems.Thm_mme_CW_square_asymptoticRank_le
import Theorems.Thm_mme_strassen_lt_three_mul_of_tau_value_surplus
import Theorems.Thm_mme_omega_eq_strassen

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

/-- Verifier-ready final reduction from the fixed square value to the
Davie--Stothers exponent bound. -/
theorem solution
    {K : Type u} [Field K] :
    matMulExp K < 23737 / 10000 := by
  rw [mme_omega_eq_strassen]
  have hR :
      tensorAsymptoticRank
        (TensorObj.kron (CWObj K 6) (CWObj K 6)) ≤ (64 : ℝ) := by
    have h := mme_CW_square_asymptoticRank_le (K := K) 6
    norm_num at h ⊢
    exact h
  have h := mme_strassen_lt_three_mul_of_tau_value_surplus
    (K := K) (T := TensorObj.kron (CWObj K 6) (CWObj K 6))
    (tau := (23737 / 30000 : ℝ))
    (V := (640000001 / 10000000 : ℝ))
    (R := (64 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hR
    mme_stothers_fourth_fixed_tau_value_23737 (by norm_num)
  norm_num at h ⊢
  exact h

