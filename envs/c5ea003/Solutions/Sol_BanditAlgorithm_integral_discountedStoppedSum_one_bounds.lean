-- Prove2me | solution 1 for BanditAlgorithm.integral_discountedStoppedSum_one_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T04:06:31.892974+00:00
-- url     : https://prove2.me/submissions/8f850f86-4797-46ff-a33d-04088ea8cb48

import Mathlib.Analysis.SpecificLimits.Normed
import Theorems.Thm_BanditAlgorithm_integrable_discountedStoppedSum_one

open MeasureTheory ProbabilityTheory
open BanditAlgorithm

private theorem summable_stopped_duration
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

private theorem stopped_duration_bounds
    {S : Type*} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ : (ℕ → S) → ℕ∞} (hτ1 : ∀ ω, 1 ≤ τ ω) (ω : ℕ → S) :
    1 ≤ discountedStoppedSum α (fun _ : S ↦ (1 : ℝ)) τ ω ∧
      discountedStoppedSum α (fun _ : S ↦ (1 : ℝ)) τ ω ≤
        ∑' t : ℕ, α ^ t := by
  let f : ℕ → ℝ :=
    fun t ↦ if (t : ℕ∞) < τ ω then α ^ t * (1 : ℝ) else 0
  have hf : Summable f := summable_stopped_duration hα0 hα1 τ ω
  have hg : Summable (fun t : ℕ ↦ α ^ t) :=
    summable_geometric_of_norm_lt_one (K := ℝ) (by
      rw [Real.norm_eq_abs, abs_of_nonneg hα0]
      exact hα1)
  constructor
  · rw [show discountedStoppedSum α (fun _ : S ↦ (1 : ℝ)) τ ω =
        ∑' t, f t by rfl, hf.tsum_eq_zero_add]
    have hzero : (0 : ℕ∞) < τ ω :=
      lt_of_lt_of_le (by norm_num) (hτ1 ω)
    have htail : 0 ≤ ∑' t : ℕ, f (t + 1) :=
      tsum_nonneg fun t ↦ by
        unfold f
        split_ifs <;> positivity
    simpa [f, hzero] using add_le_add_left htail 1
  · change (∑' t, f t) ≤ ∑' t : ℕ, α ^ t
    exact hf.tsum_le_tsum (fun t ↦ by
      unfold f
      split_ifs
      · simp
      · exact pow_nonneg hα0 t) hg

theorem solution
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (x : S)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ)
    (hτ1 : ∀ ω, 1 ≤ τ ω) :
    1 ≤ (∫ ω, discountedStoppedSum α (fun _ : S ↦ 1) τ ω
      ∂markovChainMeasure P x) ∧
    (∫ ω, discountedStoppedSum α (fun _ : S ↦ 1) τ ω
      ∂markovChainMeasure P x) ≤ ∑' t : ℕ, α ^ t := by
  letI : IsProbabilityMeasure (markovChainMeasure P x) := by
    rw [markovChainMeasure]
    infer_instance
  have hi := integrable_discountedStoppedSum_one P hα0 hα1 x hτ
  constructor
  · simpa using integral_mono (integrable_const (1 : ℝ)) hi
      (fun ω ↦ (stopped_duration_bounds hα0 hα1 hτ1 ω).1)
  · simpa using integral_mono hi
      (integrable_const (∑' t : ℕ, α ^ t))
      (fun ω ↦ (stopped_duration_bounds hα0 hα1 hτ1 ω).2)
