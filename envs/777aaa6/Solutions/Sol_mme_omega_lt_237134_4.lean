-- Prove2me | solution 4 for mme_omega_lt_237134
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T01:02:44.81918+00:00
-- url     : https://prove2.me/submissions/be9a97c8-761e-413b-8ff0-9fa622581120
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_released_witness_joint_log_recipe
import Theorems.Thm_mme_logarithmic_joint_regional_recipe_compilation
import Theorems.Thm_mme_joint_regional_CW_plan_omega_bound
import Theorems.Thm_mme_more_asymmetry_released_witness_finite_loss_reserve
import Definitions.Def_mme_omega
import Mathlib

open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

theorem solution {K : Type u} [Field K] : matMulExp K < 237134 / 100000 := by
  obtain ⟨n, ell, P, D, hn, hi, hv, ho, hd⟩ := mme_more_asymmetry_released_witness_joint_log_recipe
  obtain ⟨A, hAi, hAo, hAd⟩ := mme_logarithmic_joint_regional_recipe_compilation D
  have hvol : A.a * A.b * A.c = D.a * D.b * D.c := by
    simp only [JointPlan.a, JointPlan.b, JointPlan.c, LogJointRecipe.a, LogJointRecipe.b,
      LogJointRecipe.c, hAd]
  let tau : ℝ := 3952233 / 5000000
  have ht : 0 ≤ tau := by norm_num [tau]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hiR : 0 < (D.inputs : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hi)
  have hvR : 0 < ((D.a * D.b * D.c : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hv)
  have hr := mme_more_asymmetry_released_witness_finite_loss_reserve
  have hr' := mul_lt_mul_of_pos_left hr hnR
  have hdim := mul_le_mul_of_nonneg_left hd ht
  have hlog : Real.log (D.inputs : ℝ) + (4 * (n : ℝ)) * Real.log 7 <
      D.logOutputs + tau * Real.log ((D.a * D.b * D.c : ℕ) : ℝ) := by
    dsimp [tau] at *
    nlinarith
  have he := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_add, Real.exp_log hiR, Real.exp_add] at he
  have hpow : Real.exp (4 * (n : ℝ) * Real.log 7) = ((7 ^ (4 * n) : ℕ) : ℝ) := by
    calc
      Real.exp (4 * (n : ℝ) * Real.log 7) =
          Real.exp (((4 * n : ℕ) : ℝ) * Real.log 7) := by push_cast; rfl
      _ = Real.exp (Real.log 7) ^ (4 * n) := Real.exp_nat_mul _ _
      _ = ((7 ^ (4 * n) : ℕ) : ℝ) := by
        rw [Real.exp_log (by norm_num : (0:ℝ) < 7), Nat.cast_pow, Nat.cast_ofNat]
  rw [hpow] at he
  have hrpow : Real.exp (tau * Real.log ((D.a * D.b * D.c : ℕ) : ℝ)) =
      (((D.a * D.b * D.c : ℕ) : ℝ) ^ tau) := by
    rw [Real.rpow_def_of_pos hvR]
    congr 1
    ring
  rw [hrpow] at he
  have hmul := mul_le_mul_of_nonneg_right hAo (Real.rpow_nonneg hvR.le tau)
  have hsurplus : ((A.inputs * 7 ^ (4 * n) : ℕ) : ℝ) <
      (A.outputs : ℝ) * (((A.a * A.b * A.c : ℕ) : ℝ) ^ tau) := by
    simpa only [hAi, hvol, Nat.cast_mul] using he.trans_le hmul
  have hbound := mme_joint_regional_CW_plan_omega_bound (K := K) A tau (by simpa only [hvol] using hv) hsurplus
  have h3 : (3 : ℝ) * tau < 237134 / 100000 := by norm_num [tau]
  exact lt_trans hbound h3
