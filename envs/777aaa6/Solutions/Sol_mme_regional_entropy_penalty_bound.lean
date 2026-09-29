-- Prove2me | solution 1 for mme_regional_entropy_penalty_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T20:52:08.876039+00:00
-- url     : https://prove2.me/submissions/9f4ea761-a390-4a29-a6c9-b5d0210f45d6

import Definitions.Def_mme_regional_split_entropy_data
import Mathlib
open BigOperators MME.RegionRate MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

private theorem entropy_bits_continuous {W : Type*} [Fintype W] :
    Continuous (mme_modern_entropyBits (D := W)) := by
  unfold mme_modern_entropyBits
  exact (continuous_finset_sum _ (fun w _ ↦ Real.continuous_negMulLog.comp (continuous_apply w))).div_const _

theorem solution {half : ℕ} {parent : Fin 3 → ℕ} (alpha : Split half parent → ℝ)
    (hpos : ∀ c, 0 ≤ alpha c) (hmass : ∑ c, alpha c = 1) :
    0 ≤ entropyPenalty alpha ∧
    ∀ rho ∈ SameMarginalDistributions alpha,
      entropy rho ≤ entropy alpha + Real.log 2 * entropyPenalty alpha := by
  classical
  let box : Set (Split half parent → ℝ) := Set.pi Set.univ (fun _ ↦ Set.Icc 0 1)
  have hb : IsCompact box := isCompact_univ_pi (fun _ ↦ isCompact_Icc)
  have hsub : SameMarginalDistributions alpha ⊆ box := by
    intro rho hr
    intro c hc
    refine ⟨hr.1 c,?_⟩
    rw [← hr.2.1]
    exact Finset.single_le_sum (fun c _ ↦ hr.1 c) (Finset.mem_univ c)
  have hbound : BddAbove (mme_modern_entropyBits '' SameMarginalDistributions alpha) :=
    ((hb.image entropy_bits_continuous).bddAbove).mono (Set.image_mono hsub)
  have ha : alpha ∈ SameMarginalDistributions alpha := ⟨hpos,hmass,fun _ _ ↦ rfl⟩
  have hself := le_csSup hbound (Set.mem_image_of_mem mme_modern_entropyBits ha)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he (p : Split half parent → ℝ) : entropy p = Real.log 2 * mme_modern_entropyBits p := by
    unfold entropy mme_modern_entropyBits
    field_simp
  refine ⟨sub_nonneg.mpr hself,?_⟩
  intro rho hr
  have hh := le_csSup hbound (Set.mem_image_of_mem mme_modern_entropyBits hr)
  rw [he rho,he alpha]
  unfold entropyPenalty
  nlinarith [mul_le_mul_of_nonneg_left hh hl.le]
