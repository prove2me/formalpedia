-- Prove2me | solution 5 for mme_omega_lt_237134
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T07:30:12.513968+00:00
-- url     : https://prove2.me/submissions/6b6275da-da44-4bd8-8f04-3ec3cd38fbe9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_global_joint_finite_witness
import Theorems.Thm_mme_global_CW_joint_start_omega_bound
import Theorems.Thm_mme_more_asymmetry_released_witness_finite_loss_reserve
open MME MME.GlobalCW
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u

theorem solution {K : Type u} [Field K] :
    matMulExp K < 237134 / 100000 := by
  obtain ⟨n,ell,D,hn,hi,hv,ho,hd⟩ := mme_more_asymmetry_global_joint_finite_witness
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
  rw [Real.exp_add,Real.exp_log hiR,Real.exp_add] at he
  have hpow : Real.exp (4 * (n : ℝ) * Real.log 7) = ((7 ^ (4*n) : ℕ) : ℝ) := by
    calc
      Real.exp (4 * (n : ℝ) * Real.log 7) =
          Real.exp (((4*n : ℕ) : ℝ) * Real.log 7) := by push_cast; rfl
      _ = Real.exp (Real.log 7) ^ (4*n) := Real.exp_nat_mul _ _
      _ = ((7 ^ (4*n) : ℕ) : ℝ) := by
        rw [Real.exp_log (by norm_num : (0:ℝ)<7),Nat.cast_pow,Nat.cast_ofNat]
  rw [hpow] at he
  have hrpow : Real.exp (tau * Real.log ((D.a * D.b * D.c : ℕ) : ℝ)) =
      (((D.a * D.b * D.c : ℕ) : ℝ) ^ tau) := by
    rw [Real.rpow_def_of_pos hvR]
    congr 1
    ring
  rw [hrpow] at he
  have hsurplus : ((D.inputs * 7 ^ (4*n) : ℕ) : ℝ) <
      Real.exp D.logOutputs * (((D.a * D.b * D.c : ℕ) : ℝ) ^ tau) := by
    simpa only [Nat.cast_mul] using he
  have homega := mme_global_CW_joint_start_omega_bound (K := K) D tau hv hsurplus
  have hgap : 3 * tau < (237134 : ℝ) / 100000 := by norm_num [tau]
  exact homega.trans hgap
