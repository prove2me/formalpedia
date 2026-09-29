-- Prove2me | solution 1 for Probability.AdaptiveQS.skip_throughput_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T20:10:17.482891+00:00
-- url     : https://prove2.me/submissions/ad656e27-c96c-403b-beae-900a0cb23df7

import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSSkipFlip

open Probability.AdaptiveQS Finset in
theorem solution {ι : Type*} [DecidableEq ι] {s : Finset ι} {d r : ι → ℝ}
    (hc : Concordant s d r) (θ : ℝ) (hK : (keepSet s d θ).Nonempty) :
    throughput s r ≤ throughput (keepSet s d θ) r := by
  classical
  have hsplit : s = keepSet s d θ ∪ skipSet s d θ := by
    ext i
    simp only [keepSet, skipSet, Finset.mem_union, Finset.mem_filter]
    tauto
  have hdisj : Disjoint (keepSet s d θ) (skipSet s d θ) := by
    rw [keepSet, skipSet]
    exact Finset.disjoint_filter.2 (fun i _ h1 h2 => h2 h1)
  have hcmp : ∀ i ∈ keepSet s d θ, ∀ j ∈ skipSet s d θ, r j ≤ r i := by
    intro i hi j hj
    rw [keepSet, Finset.mem_filter] at hi
    rw [skipSet, Finset.mem_filter] at hj
    exact hc i hi.1 j hj.1 (by linarith [not_le.1 hj.2])
  -- double counting: |K| Σ_S r ≤ |S| Σ_K r
  have hdouble : ((keepSet s d θ).card : ℝ) * ∑ j ∈ skipSet s d θ, r j
      ≤ ((skipSet s d θ).card : ℝ) * ∑ i ∈ keepSet s d θ, r i := by
    have h1 : ((keepSet s d θ).card : ℝ) * ∑ j ∈ skipSet s d θ, r j
        = ∑ i ∈ keepSet s d θ, ∑ j ∈ skipSet s d θ, r j := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : ((skipSet s d θ).card : ℝ) * ∑ i ∈ keepSet s d θ, r i
        = ∑ i ∈ keepSet s d θ, ∑ j ∈ skipSet s d θ, r i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [h1, h2]
    exact Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hcmp i hi j hj))
  have hKpos : (0 : ℝ) < (keepSet s d θ).card := by exact_mod_cast hK.card_pos
  unfold throughput
  rw [hsplit, Finset.sum_union hdisj, Finset.card_union_of_disjoint hdisj]
  have hkeep : keepSet (keepSet s d θ ∪ skipSet s d θ) d θ = keepSet s d θ := by
    ext i
    simp only [keepSet, skipSet, Finset.mem_union, Finset.mem_filter]
    tauto
  rw [hkeep]
  push_cast
  have hden : (0 : ℝ) < ((keepSet s d θ).card : ℝ) + ((skipSet s d θ).card : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) (skipSet s d θ).card
    linarith
  rw [div_le_div_iff₀ hden hKpos]
  nlinarith [hdouble]
