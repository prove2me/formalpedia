-- Prove2me | solution 1 for BanditAlgorithm.gittins_epsilon_optimal_stopping
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T03:01:33.909352+00:00
-- url     : https://prove2.me/submissions/758040a7-98e3-4601-80d3-3175ab56d666

import Theorems.Thm_BanditAlgorithm_gittins_stopping_ratio_le_index

open MeasureTheory ProbabilityTheory ENNReal
open BanditAlgorithm

/-- The stopping-time supremum defining the Gittins index admits arbitrarily
close admissible witnesses. -/
theorem solution
    {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α) (x : S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : (ℕ → S) → ℕ∞,
      IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      gittinsIndex P r α x - ε <
        (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P x) /
          (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω
            ∂markovChainMeasure P x) := by
  let A : Set ℝ := {g : ℝ | ∃ τ : (ℕ → S) → ℕ∞,
    IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
    g = (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P x) /
        (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω
          ∂markovChainMeasure P x)}
  have hAne : A.Nonempty := by
    let τ : (ℕ → S) → ℕ∞ := fun _ ↦ 1
    refine ⟨(∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P x) /
        (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω
          ∂markovChainMeasure P x), τ, ?_, ?_, rfl⟩
    · intro n
      change MeasurableSet[trajectoryFiltration S n] {ω | (1 : ℕ∞) ≤ n}
      by_cases hn : 1 ≤ n
      · convert MeasurableSet.univ
        ext ω
        simp [hn]
      · convert MeasurableSet.empty
        ext ω
        simp [hn]
    · intro ω
      rfl
  have hAbdd : BddAbove A := by
    refine ⟨gittinsIndex P r α x, ?_⟩
    intro g hg
    rcases hg with ⟨τ, hτ, hτ1, rfl⟩
    exact gittins_stopping_ratio_le_index P hr hα0 hα1 hint x τ hτ hτ1
  have hsup : sSup A = gittinsIndex P r α x := by
    rfl
  have hlt : gittinsIndex P r α x - ε < sSup A := by
    rw [hsup]
    linarith
  rcases (lt_csSup_iff hAbdd hAne).mp hlt with ⟨g, hg, hgg⟩
  rcases hg with ⟨τ, hτ, hτ1, rfl⟩
  exact ⟨τ, hτ, hτ1, hgg⟩
