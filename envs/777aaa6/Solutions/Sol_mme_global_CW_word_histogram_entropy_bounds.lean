-- Prove2me | solution 1 for mme_global_CW_word_histogram_entropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T08:48:57.611134+00:00
-- url     : https://prove2.me/submissions/af879a01-9671-4d4b-9144-b4b23cb89fd6

import Definitions.Def_mme_global_CW_entropy_data
import Theorems.Thm_mme_regional_histogram_entropy_bounds
import Theorems.Thm_mme_regional_target_marginals
open BigOperators MME MME.GlobalCW MME.RegionRate MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem solution {ell M : ℕ} (D : CountedStage ell M) (i : Fin 3) :
    (modeNumber i (D.mu i) : ℝ) ≤ Real.exp (D.wordPotential i) ∧
    Real.exp (D.wordPotential i) ≤
      polynomialFactor D.n (D.R * (D.degree+1) * Fintype.card (CompleteSplit.CompleteWord ell)) *
        modeNumber i (D.mu i) := by
  classical
  have hm := (mme_regional_target_marginals D.m i D.reference D.reference_target).1
  have hmass : (∑ c : Cell D.degree D.R D.bounds, ∑ w, D.mu i c w) = ∑ r, D.n r := by
    simp only [D.mass]
    rw [Fintype.sum_sigma]
    simp only [hm]
  have hbound (g : Fin D.R × Fin (D.degree+1)) :
      ∑ w, aggregate i (D.mu i) g.1 g.2 w ≤ ∑ r, D.n r := by
    unfold aggregate
    rw [Finset.sum_comm,← hmass]
    apply Finset.sum_le_sum
    intro c _
    apply Finset.sum_le_sum
    intro w _
    split_ifs <;> omega
  have h := mme_regional_histogram_entropy_bounds
    (fun g : Fin D.R × Fin (D.degree+1) ↦ aggregate i (D.mu i) g.1 g.2)
    (∑ r, D.n r) hbound
  simpa only [modeNumber,CountedStage.wordPotential,polynomialFactor,Fintype.card_prod,
    Fintype.card_fin] using h
