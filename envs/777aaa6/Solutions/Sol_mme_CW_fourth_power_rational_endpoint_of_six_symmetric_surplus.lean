-- Prove2me | solution 1 for mme_CW_fourth_power_rational_endpoint_of_six_symmetric_surplus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T17:19:35.994241+00:00
-- url     : https://prove2.me/submissions/3021f40d-eada-4837-b192-210b0390127f

import Theorems.Thm_mme_CW_fourth_power_rank_and_six_symmetry
import Theorems.Thm_mme_six_symmetric_tau_value_to_direct_of_iso
import Theorems.Thm_mme_strassen_lt_three_mul_of_tau_value_surplus
import Theorems.Thm_mme_omega_eq_strassen

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (q N : ℕ) (hN : 0 < N)
    (tau : ℝ) (bound : ℚ)
    (htau : 0 < tau) (hbound : 3 * tau ≤ (bound : ℝ))
    (hsurplus : ∃ V : ℝ, (((q : ℝ) + 2) ^ (4 : ℕ)) ^ N < V ∧
      HasSixSymmetricTauValueAtLeast
        ((MME.StothersFourth.cwFourthObj K q).kronPow N) tau V) :
    matMulExp K < (bound : ℝ) := by
  obtain ⟨V, hV, hvalue⟩ := hsurplus
  obtain ⟨hrank, hsym⟩ := mme_CW_fourth_power_rank_and_six_symmetry (K := K) q N hN
  have hbase : (1 : ℝ) ≤ (q : ℝ) + 2 := by
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  have hbudget : (1 : ℝ) ≤ (((q : ℝ) + 2) ^ (4 : ℕ)) ^ N :=
    one_le_pow₀ (one_le_pow₀ hbase)
  have hnonneg : 0 ≤ V := by linarith
  have hdirect : HasTauValueAtLeast
      ((MME.StothersFourth.cwFourthObj K q).kronPow N) tau V :=
    mme_six_symmetric_tau_value_to_direct_of_iso
      ((MME.StothersFourth.cwFourthObj K q).kronPow N) tau V hnonneg hsym hvalue
  have hexponent : matMulExp_strassen K < 3 * tau :=
    mme_strassen_lt_three_mul_of_tau_value_surplus
      (K := K) (T := (MME.StothersFourth.cwFourthObj K q).kronPow N)
      (tau := tau) (V := V) (R := (((q : ℝ) + 2) ^ (4 : ℕ)) ^ N)
      htau (by linarith) (by linarith) hrank hdirect hV
  rw [mme_omega_eq_strassen]
  exact hexponent.trans_le hbound
