-- Prove2me | solution 1 for BanditAlgorithm.integrable_discountedStoppedSum_one
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T04:01:49.28374+00:00
-- url     : https://prove2.me/submissions/9ca26a33-dce8-495e-8b58-6834f998157a

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_GittinsIndex

open MeasureTheory ProbabilityTheory
open BanditAlgorithm

private theorem trajectoryFiltration_le_one
    {S : Type*} [MeasurableSpace S] (n : ℕ) :
    trajectoryFiltration S n ≤ (inferInstance : MeasurableSpace (ℕ → S)) := by
  intro s hs
  rcases hs with ⟨u, hu, rfl⟩
  exact hu.preimage (by
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply i.1)

private theorem measurable_stopped_one
    {S : Type*} [MeasurableSpace S] {α : ℝ}
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) :
    Measurable (discountedStoppedSum α (fun _ : S ↦ 1) τ) := by
  unfold discountedStoppedSum
  apply Measurable.tsum
  intro t
  apply Measurable.ite
  · rw [show {ω | (t : ℕ∞) < τ ω} =
        {ω | τ ω ≤ (t : ℕ∞)}ᶜ by ext ω; simp]
    exact ((trajectoryFiltration_le_one t) _ (hτ t)).compl
  · fun_prop
  · fun_prop

private theorem summable_stopped_one'
    {S : Type*} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    Summable (fun t : ℕ ↦
      if (t : ℕ∞) < τ ω then α ^ t * (1 : ℝ) else 0) := by
  apply Summable.of_norm_bounded
    (summable_geometric_of_norm_lt_one (K := ℝ) (by
      rw [Real.norm_eq_abs, abs_of_nonneg hα0]
      exact hα1))
  intro t
  by_cases ht : (t : ℕ∞) < τ ω
  · simp [ht, abs_of_nonneg hα0]
  · simp [ht, pow_nonneg hα0 t]

theorem solution
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (x : S)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) :
    Integrable (discountedStoppedSum α (fun _ : S ↦ 1) τ)
      (markovChainMeasure P x) := by
  letI : IsProbabilityMeasure (markovChainMeasure P x) := by
    rw [markovChainMeasure]
    infer_instance
  have hgeom : Summable (fun t : ℕ ↦ α ^ t) :=
    summable_geometric_of_norm_lt_one (K := ℝ) (by
      rw [Real.norm_eq_abs, abs_of_nonneg hα0]
      exact hα1)
  apply (integrable_const (∑' t : ℕ, α ^ t)).mono
    (measurable_stopped_one hτ).aestronglyMeasurable
  filter_upwards with ω
  let f : ℕ → ℝ :=
    fun t ↦ if (t : ℕ∞) < τ ω then α ^ t * (1 : ℝ) else 0
  have hnorm : ∀ t, ‖f t‖ ≤ α ^ t := by
    intro t
    by_cases ht : (t : ℕ∞) < τ ω
    · simp [f, ht, abs_of_nonneg hα0]
    · simp [f, ht, pow_nonneg hα0 t]
  have hfsum := summable_stopped_one' hα0 hα1 τ ω
  calc
    ‖discountedStoppedSum α (fun _ : S ↦ 1) τ ω‖ =
        ‖∑' t, f t‖ := rfl
    _ ≤ ∑' t, ‖f t‖ := norm_tsum_le_tsum_norm hfsum.norm
    _ ≤ ∑' t, α ^ t := hfsum.norm.tsum_le_tsum hnorm hgeom
    _ = ‖∑' t, α ^ t‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact tsum_nonneg fun t ↦ pow_nonneg hα0 t
