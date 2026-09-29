-- Prove2me | solution 1 for Probability.AdaptiveQS.skip_throughput_gt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T00:24:48.588459+00:00
-- url     : https://prove2.me/submissions/aa72ba5f-aa0c-45a8-8f5f-e574ff1cb7b6

import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSSkipFlip
open Finset Probability.AdaptiveQS in
theorem solution {ι : Type*} [DecidableEq ι] {s : Finset ι} {d r : ι → ℝ} (hc : Concordant s d r)
    (θ : ℝ) {i₀ j₀ : ι} (hi₀ : i₀ ∈ keepSet s d θ) (hj₀ : j₀ ∈ skipSet s d θ) (hlt : r j₀ < r i₀) :
    throughput s r < throughput (keepSet s d θ) r := by
  unfold throughput
  -- `s` splits into kept and skipped targets
  have hsum : ∑ i ∈ s, r i = ∑ i ∈ keepSet s d θ, r i + ∑ i ∈ skipSet s d θ, r i :=
    (sum_filter_add_sum_filter_not s (fun i => θ ≤ d i) r).symm
  have hcard : s.card = (keepSet s d θ).card + (skipSet s d θ).card :=
    (card_filter_add_card_filter_not (fun i => θ ≤ d i)).symm
  have hKpos : 0 < (keepSet s d θ).card := card_pos.2 ⟨i₀, hi₀⟩
  have hJpos : 0 < (skipSet s d θ).card := card_pos.2 ⟨j₀, hj₀⟩
  -- every skipped rate is at most every kept rate (concordance)
  have hdom : ∀ j ∈ skipSet s d θ, ∀ k ∈ keepSet s d θ, r j ≤ r k := by
    intro j hj k hk
    have hj' := mem_filter.1 hj
    have hk' := mem_filter.1 hk
    exact hc k hk'.1 j hj'.1 (by linarith [not_le.1 hj'.2, hk'.2])
  have hpair : ((skipSet s d θ).card : ℝ) * ∑ k ∈ keepSet s d θ, r k
      - ((keepSet s d θ).card : ℝ) * ∑ j ∈ skipSet s d θ, r j
      = ∑ j ∈ skipSet s d θ, ∑ k ∈ keepSet s d θ, (r k - r j) := by
    simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_sum]
  have hpos : 0 < ∑ j ∈ skipSet s d θ, ∑ k ∈ keepSet s d θ, (r k - r j) := by
    refine sum_pos' (fun j hj => sum_nonneg (fun k hk => sub_nonneg.2 (hdom j hj k hk))) ⟨j₀, hj₀, ?_⟩
    exact sum_pos' (fun k hk => sub_nonneg.2 (hdom j₀ hj₀ k hk)) ⟨i₀, hi₀, sub_pos.2 hlt⟩
  have hKR : (0 : ℝ) < (keepSet s d θ).card := by exact_mod_cast hKpos
  have hJR : (0 : ℝ) < (skipSet s d θ).card := by exact_mod_cast hJpos
  rw [hsum, hcard, Nat.cast_add, div_lt_div_iff₀ (by linarith) hKR]
  nlinarith [hpair, hpos]
