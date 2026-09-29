-- Prove2me | solution 1 for mme_CW_fourth_rational_endpoint_of_six_symmetric_surplus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T17:19:34.518843+00:00
-- url     : https://prove2.me/submissions/9f93a76f-257c-4851-82aa-cee819cec9aa

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
    {K : Type u} [Field K] (q : ℕ) (tau : ℝ) (bound : ℚ)
    (htau : 0 < tau) (hbound : 3 * tau ≤ (bound : ℝ))
    (hsurplus : ∃ V : ℝ, ((q : ℝ) + 2) ^ (4 : ℕ) < V ∧
      HasSixSymmetricTauValueAtLeast (MME.StothersFourth.cwFourthObj K q) tau V) :
    matMulExp K < (bound : ℝ) := by
  obtain ⟨V, hV, hvalue⟩ := hsurplus
  have hbase : (1 : ℝ) ≤ (q : ℝ) + 2 := by
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  have hbudget : (1 : ℝ) ≤ ((q : ℝ) + 2) ^ (4 : ℕ) := one_le_pow₀ hbase
  have hnonneg : 0 ≤ V := by linarith
  have hdirect : HasTauValueAtLeast (MME.StothersFourth.cwFourthObj K q) tau V :=
    mme_six_symmetric_tau_value_to_direct_of_iso
      (MME.StothersFourth.cwFourthObj K q) tau V hnonneg
      (mme_CW_fourth_six_symmetrization_iso q) hvalue
  have hexponent : matMulExp_strassen K < 3 * tau :=
    mme_strassen_lt_three_mul_of_tau_value_surplus
      (K := K) (T := MME.StothersFourth.cwFourthObj K q)
      (tau := tau) (V := V) (R := ((q : ℝ) + 2) ^ (4 : ℕ))
      htau (by linarith) (by linarith)
      (mme_CW_fourth_asymptoticRank_le q) hdirect hV
  rw [mme_omega_eq_strassen]
  exact hexponent.trans_le hbound
