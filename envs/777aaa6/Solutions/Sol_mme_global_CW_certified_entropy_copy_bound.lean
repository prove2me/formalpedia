-- Prove2me | solution 1 for mme_global_CW_certified_entropy_copy_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T08:59:14.930898+00:00
-- url     : https://prove2.me/submissions/d07d33cc-a172-45db-a9a3-67f8a0ee59e8

import Definitions.Def_mme_global_CW_entropy_data
import Theorems.Thm_mme_global_CW_common_scale_entropy_bound
import Theorems.Thm_mme_regional_target_entropy_bounds
open BigOperators MME MME.GlobalCW MME.RegionRate MME.RegionRealization MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem solution {ell M : ℕ} (D : CountedStage ell M) :
    D.entropyLogCopies ≤ D.certifiedLogCopies := by
  have hs := mme_global_CW_common_scale_entropy_bound D
  have ht := (mme_regional_target_entropy_bounds D.m 0 D.reference D.reference_target).2.1
  have hQ : 0 < (D.scale : ℝ) := by
    apply Nat.cast_pos.mpr
    unfold CountedStage.scale commonScale
    exact (Nat.succ_pos D.degree).trans_le (le_max_left _ _)
  have hP : 0 < polynomialFactor D.n (Fintype.card (Cell D.degree D.R D.bounds)) := by
    unfold polynomialFactor
    positivity
  have hF : 0 < D.entropyScaleFactor := by
    unfold CountedStage.entropyScaleFactor CountedStage.entropyLoadFactor polynomialFactor ambientFactor
    positivity
  have hT : 0 < ((RecursiveXHash.target (n := D.n) D.m).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨D.reference,D.reference_target⟩
  have ht' : Real.exp (jointPotential D.m) ≤
      polynomialFactor D.n (Fintype.card (Cell D.degree D.R D.bounds)) *
        ((RecursiveXHash.target (n := D.n) D.m).card : ℝ) := by
    simpa only [polynomialFactor,Fintype.card_eq_nat_card] using ht
  have hlogT := Real.log_le_log (Real.exp_pos _) ht'
  rw [Real.log_exp,Real.log_mul (ne_of_gt hP) (ne_of_gt hT)] at hlogT
  have hlogQ := Real.log_le_log hQ hs.2
  rw [Real.log_mul (ne_of_gt hF) (ne_of_gt (Real.exp_pos _)),Real.log_exp] at hlogQ
  have hsqrt := Real.sqrt_le_sqrt hlogQ
  have h64Q : Real.log (64 * (D.scale : ℝ)) = Real.log 64 + Real.log D.scale :=
    Real.log_mul (by norm_num) (ne_of_gt hQ)
  have h64F : Real.log (64 * D.entropyScaleFactor) = Real.log 64 + Real.log D.entropyScaleFactor :=
    Real.log_mul (by norm_num) (ne_of_gt hF)
  unfold CountedStage.entropyLogCopies CountedStage.certifiedLogCopies
  rw [h64Q,h64F]
  unfold CountedStage.entropyExponent at hlogQ hsqrt ⊢
  linarith
