-- Prove2me | solution 1 for MarkovChainCLT.phiMixingCoef_comp_nonneg_le_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T15:43:20.147355+00:00
-- url     : https://prove2.me/submissions/af95860f-0e95-4a86-9f8c-d348d3baa519

import Theorems.Thm_MarkovChainCLT_processSigma_comp_le

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {Ω X E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace E] (P : Measure Ω) [IsFiniteMeasure P]
    (Y : ℕ → Ω → X) (g : X → E) (hg : Measurable g) (n : ℕ) :
    0 ≤ phiMixingCoef P (fun i ω => g (Y i ω)) n ∧
      phiMixingCoef P (fun i ω => g (Y i ω)) n ≤ phiMixingCoef P Y n := by
  set Sg := {r | ∃ k : ℕ, ∃ A B : Set Ω,
      MeasurableSet[processSigma (fun i ω => g (Y i ω)) (Set.Iic k)] A ∧ P A ≠ 0 ∧
      MeasurableSet[processSigma (fun i ω => g (Y i ω)) (Set.Ici (k + n))] B ∧
      r = |(P (A ∩ B)).toReal / (P A).toReal - (P B).toReal|} with hSg
  set SY := {r | ∃ k : ℕ, ∃ A B : Set Ω,
      MeasurableSet[processSigma Y (Set.Iic k)] A ∧ P A ≠ 0 ∧
      MeasurableSet[processSigma Y (Set.Ici (k + n))] B ∧
      r = |(P (A ∩ B)).toReal / (P A).toReal - (P B).toReal|} with hSY
  have hsub : Sg ⊆ SY := by
    rintro r ⟨k, A, B, hA, hA0, hB, rfl⟩
    exact ⟨k, A, B, processSigma_comp_le Y g hg _ _ hA, hA0,
      processSigma_comp_le Y g hg _ _ hB, rfl⟩
  have hbddY : BddAbove SY := by
    refine ⟨1 + (P Set.univ).toReal, ?_⟩
    rintro r ⟨k, A, B, hA, hA0, hB, rfl⟩
    have hApos : (0:ℝ) < (P A).toReal :=
      ENNReal.toReal_pos hA0 (measure_ne_top P A)
    have hratio : (P (A ∩ B)).toReal / (P A).toReal ≤ 1 := by
      rw [div_le_one hApos]
      exact ENNReal.toReal_mono (measure_ne_top P A) (measure_mono Set.inter_subset_left)
    have hr0 : (0:ℝ) ≤ (P (A ∩ B)).toReal / (P A).toReal :=
      div_nonneg ENNReal.toReal_nonneg hApos.le
    have hB1 : (P B).toReal ≤ (P Set.univ).toReal :=
      ENNReal.toReal_mono (measure_ne_top P _) (measure_mono (Set.subset_univ B))
    have hB0 : (0:ℝ) ≤ (P B).toReal := ENNReal.toReal_nonneg
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hbddg : BddAbove Sg := hbddY.mono hsub
  have hnonneg : ∀ S : Set ℝ, BddAbove S → (∀ r ∈ S, (0:ℝ) ≤ r) → (0:ℝ) ≤ sSup S := by
    intro S hb hpos
    rcases S.eq_empty_or_nonempty with rfl | ⟨r, hr⟩
    · simp
    · exact le_trans (hpos r hr) (le_csSup hb hr)
  constructor
  · exact hnonneg Sg hbddg (by rintro r ⟨k, A, B, hA, hA0, hB, rfl⟩; exact abs_nonneg _)
  · rcases Sg.eq_empty_or_nonempty with h | hne
    · rw [show phiMixingCoef P (fun i ω => g (Y i ω)) n = sSup Sg from rfl, h]
      simpa using hnonneg SY hbddY
        (by rintro r ⟨k, A, B, hA, hA0, hB, rfl⟩; exact abs_nonneg _)
    · exact csSup_le_csSup hbddY hne hsub
