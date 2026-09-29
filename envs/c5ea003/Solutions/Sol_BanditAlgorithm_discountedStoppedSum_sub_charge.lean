-- Prove2me | solution 1 for BanditAlgorithm.discountedStoppedSum_sub_charge
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T03:45:40.136921+00:00
-- url     : https://prove2.me/submissions/27a8ac60-5627-4471-a813-298e92fae9c9

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_GittinsIndex

open MeasureTheory ProbabilityTheory ENNReal
open BanditAlgorithm

private theorem summable_stopped_one
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

private theorem summable_stopped_reward
    {S : Type*} {α : ℝ} (hα0 : 0 ≤ α)
    (r : S → ℝ) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S)
    (hsum : Summable (fun t : ℕ ↦ α ^ t * |r (ω t)|)) :
    Summable (fun t : ℕ ↦
      if (t : ℕ∞) < τ ω then α ^ t * r (ω t) else 0) := by
  apply Summable.of_norm_bounded hsum
  intro t
  by_cases ht : (t : ℕ∞) < τ ω
  · simp [ht, abs_of_nonneg hα0]
  · simp [ht, mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)]

theorem solution
    {S : Type*} {α γ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (r : S → ℝ) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S)
    (hsum : Summable (fun t : ℕ ↦ α ^ t * |r (ω t)|)) :
    discountedStoppedSum α (fun y ↦ r y - γ) τ ω =
      discountedStoppedSum α r τ ω -
        γ * discountedStoppedSum α (fun _ : S ↦ 1) τ ω := by
  let f : ℕ → ℝ :=
    fun t ↦ if (t : ℕ∞) < τ ω then α ^ t * r (ω t) else 0
  let d : ℕ → ℝ :=
    fun t ↦ if (t : ℕ∞) < τ ω then α ^ t * (1 : ℝ) else 0
  have hf : Summable f := summable_stopped_reward hα0 r τ ω hsum
  have hd : Summable d := summable_stopped_one hα0 hα1 τ ω
  have hterm : (fun t : ℕ ↦
      if (t : ℕ∞) < τ ω then α ^ t * (r (ω t) - γ) else 0) =
      fun t ↦ f t - γ * d t := by
    funext t
    by_cases ht : (t : ℕ∞) < τ ω
    · simp [f, d, ht]
      ring
    · simp [f, d, ht]
  change (∑' t : ℕ, if (t : ℕ∞) < τ ω then
    α ^ t * (r (ω t) - γ) else 0) = (∑' t, f t) - γ * ∑' t, d t
  rw [hterm, hf.tsum_sub (hd.mul_left γ), tsum_mul_left]
