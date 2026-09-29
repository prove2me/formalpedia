-- Prove2me | solution 1 for mme_global_CW_uniform_entropy_family_extraction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T09:01:21.811066+00:00
-- url     : https://prove2.me/submissions/ed703fbd-46de-47a1-b160-d41556360204

import Definitions.Def_mme_global_CW_entropy_data
import Definitions.Def_mme_global_CW_joint_start_data
import Theorems.Thm_mme_global_CW_certified_entropy_copy_bound
import Theorems.Thm_mme_global_CW_counted_profile_family_extraction
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.GlobalCW MME.RegionRate MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000
universe u

theorem solution {K : Type u} [Field K] {M ell types : ℕ} (T : Predicate M)
    (steps : Fin types → CountedStage ell M)
    (rate E J P F h : ℝ) (hrate : 0 ≤ rate)
    (hbudget : rate ≤ E - Real.log P - Real.log (64 * F) -
      4 * Real.sqrt (Real.log F + J - E) - h * Real.log 8)
    (hE : ∀ j, E ≤ (steps j).entropyRate)
    (hJ : ∀ j, jointPotential (steps j).m ≤ J)
    (hP : ∀ j, polynomialFactor (steps j).n
      (Fintype.card (Cell (steps j).degree (steps j).R (steps j).bounds)) ≤ P)
    (hF : ∀ j, (steps j).entropyScaleFactor ≤ F)
    (hh : ∀ j, ((steps j).repairExponent : ℝ) ≤ h)
    (inside : ∀ j i x, (steps j).output i x → T i x)
    (cover : ∀ x : Fin 3 → FineWord M, supported x → (∀ i, T i (x i)) →
      ∃! j, ∀ i, (steps j).output i (x i)) :
    ∃ D : GlobalCW.Part M ell T, D.inputs = types ∧ D.rate = rate ∧
      Restrict (bigAdd (fun _ : Fin ⌈Real.exp rate⌉₊ ↦ tensor K T))
        (bigAdd (fun _ : Fin types ↦ tensor K (fun _ (_ : FineWord M) ↦ True))) := by
  apply mme_global_CW_counted_profile_family_extraction T steps rate hrate _ inside cover
  intro j
  apply le_trans _ (mme_global_CW_certified_entropy_copy_bound (steps j))
  have hp : 0 < polynomialFactor (steps j).n
      (Fintype.card (Cell (steps j).degree (steps j).R (steps j).bounds)) := by
    unfold polynomialFactor
    positivity
  have hf : 0 < (steps j).entropyScaleFactor := by
    unfold CountedStage.entropyScaleFactor CountedStage.entropyLoadFactor polynomialFactor ambientFactor
    positivity
  have hlogP := Real.log_le_log hp (hP j)
  have hlogF := Real.log_le_log hf (hF j)
  have hlog64 := Real.log_le_log (by positivity : 0 < 64 * (steps j).entropyScaleFactor)
    (mul_le_mul_of_nonneg_left (hF j) (by norm_num : (0 : ℝ) ≤ 64))
  have hsqrt : Real.sqrt (Real.log (steps j).entropyScaleFactor + (steps j).entropyExponent) ≤
      Real.sqrt (Real.log F + J - E) := by
    apply Real.sqrt_le_sqrt
    unfold CountedStage.entropyExponent
    linarith [hJ j,hE j]
  have hrepair := mul_le_mul_of_nonneg_right (hh j)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8))
  unfold CountedStage.entropyLogCopies
  linarith [hE j]
