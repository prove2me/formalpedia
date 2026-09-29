-- Prove2me | solution 1 for MarkovChainCLT.alphaMixingCoef_comp_nonneg_le_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T15:42:44.86345+00:00
-- url     : https://prove2.me/submissions/c9dd8deb-e129-40f5-aeaf-8c619c0d2ba8

import Theorems.Thm_MarkovChainCLT_processSigma_comp_le

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {Ω X E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace E] (P : Measure Ω) [IsFiniteMeasure P]
    (Y : ℕ → Ω → X) (g : X → E) (hg : Measurable g) (n : ℕ) :
    0 ≤ alphaMixingCoef P (fun i ω => g (Y i ω)) n ∧
      alphaMixingCoef P (fun i ω => g (Y i ω)) n ≤ alphaMixingCoef P Y n := by
  set Sg := {r | ∃ k : ℕ, ∃ A B : Set Ω,
      MeasurableSet[processSigma (fun i ω => g (Y i ω)) (Set.Iic k)] A ∧
      MeasurableSet[processSigma (fun i ω => g (Y i ω)) (Set.Ici (k + n))] B ∧
      r = |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal|} with hSg
  set SY := {r | ∃ k : ℕ, ∃ A B : Set Ω,
      MeasurableSet[processSigma Y (Set.Iic k)] A ∧
      MeasurableSet[processSigma Y (Set.Ici (k + n))] B ∧
      r = |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal|} with hSY
  have hsub : Sg ⊆ SY := by
    rintro r ⟨k, A, B, hA, hB, rfl⟩
    exact ⟨k, A, B, processSigma_comp_le Y g hg _ _ hA,
      processSigma_comp_le Y g hg _ _ hB, rfl⟩
  have hbnd : ∀ s : Set Ω, (P s).toReal ≤ (P Set.univ).toReal := fun s =>
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono (Set.subset_univ s))
  have hnn : ∀ s : Set Ω, (0:ℝ) ≤ (P s).toReal := fun _ => ENNReal.toReal_nonneg
  have hbddY : BddAbove SY := by
    refine ⟨(P Set.univ).toReal + (P Set.univ).toReal * (P Set.univ).toReal, ?_⟩
    rintro r ⟨k, A, B, hA, hB, rfl⟩
    have h1 := hbnd (A ∩ B); have h2 := hbnd A; have h3 := hbnd B
    have n1 := hnn (A ∩ B); have n2 := hnn A; have n3 := hnn B
    rw [abs_sub_le_iff]
    constructor <;> nlinarith
  have hne : (0:ℝ) ∈ Sg := by
    refine ⟨0, ∅, ∅,
      @MeasurableSet.empty Ω (processSigma (fun i ω => g (Y i ω)) (Set.Iic 0)),
      @MeasurableSet.empty Ω (processSigma (fun i ω => g (Y i ω)) (Set.Ici (0 + n))), ?_⟩
    simp
  have hbddg : BddAbove Sg := hbddY.mono hsub
  exact ⟨le_csSup hbddg hne, csSup_le_csSup hbddY ⟨0, hne⟩ hsub⟩
