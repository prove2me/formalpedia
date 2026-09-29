-- Prove2me | solution 1 for MarkovChainCLT.alphaMixingCoef_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T10:08:26.399013+00:00
-- url     : https://prove2.me/submissions/25c55b47-e0b3-4fc8-a8d1-118732415448

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

/-!
`0 ≤ α(n)`: the defining set of the strong mixing coefficient contains `0`
(take `A = B = ∅`), so either the set is bounded above and its supremum dominates `0`,
or it is unbounded and the supremum is `0` by the Lean convention for `sSup`.
-/

theorem solution {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) :
    0 ≤ alphaMixingCoef P Y n := by
  set S : Set ℝ := {r | ∃ k : ℕ, ∃ A B : Set Ω,
      MeasurableSet[processSigma Y (Set.Iic k)] A ∧
      MeasurableSet[processSigma Y (Set.Ici (k + n))] B ∧
      r = |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal|} with hS
  have hmem : (0 : ℝ) ∈ S :=
    ⟨0, ∅, ∅, @MeasurableSet.empty Ω (processSigma Y (Set.Iic 0)),
      @MeasurableSet.empty Ω (processSigma Y (Set.Ici (0 + n))), by simp⟩
  by_cases hbdd : BddAbove S
  · exact le_csSup hbdd hmem
  · rw [alphaMixingCoef, ← hS, Real.sSup_of_not_bddAbove hbdd]
