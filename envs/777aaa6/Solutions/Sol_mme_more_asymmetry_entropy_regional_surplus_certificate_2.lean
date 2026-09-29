-- Prove2me | solution 2 for mme_more_asymmetry_entropy_regional_surplus_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T20:12:22.061534+00:00
-- url     : https://prove2.me/submissions/b784c95d-5748-4dd2-9e0c-408815aad3d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_released_witness_finite_log_recipe
import Theorems.Thm_mme_logarithmic_regional_recipe_compilation
import Theorems.Thm_mme_more_asymmetry_released_witness_finite_loss_reserve
import Mathlib
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem solution :
    ∃ (N ell : ℕ) (P : Predicate N) (D : EntropyRecipe N ell P),
      1 ≤ D.a * D.b * D.c ∧
      ((D.inputs * 7 ^ N : ℕ) : ℝ) <
        (D.outputs : ℝ) * (((D.a * D.b * D.c : ℕ) : ℝ) ^ ((3952233 : ℝ) / 5000000)) := by
  obtain ⟨n,ell,P,D,hn,hi,hv,ho,hd⟩ :=
    mme_more_asymmetry_released_witness_finite_log_recipe
  obtain ⟨A,hAi,hAo,hAd⟩ := mme_logarithmic_regional_recipe_compilation D
  have hvol : A.a * A.b * A.c = D.a * D.b * D.c := by
    simp only [EntropyRecipe.a,EntropyRecipe.b,EntropyRecipe.c,
      LogRecipe.a,LogRecipe.b,LogRecipe.c,hAd]
  refine ⟨4*n,ell,P,A,by simpa only [hvol] using hv,?_⟩
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
  have hmul := mul_le_mul_of_nonneg_right hAo
    (Real.rpow_nonneg hvR.le tau)
  simpa only [hAi,hvol,Nat.cast_mul,tau] using he.trans_le hmul
