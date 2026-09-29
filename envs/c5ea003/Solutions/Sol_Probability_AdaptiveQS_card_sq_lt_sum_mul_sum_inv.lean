-- Prove2me | solution 1 for Probability.AdaptiveQS.card_sq_lt_sum_mul_sum_inv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:20:00.710496+00:00
-- url     : https://prove2.me/submissions/35ca84c0-ed5d-42fc-af46-b9f82f5a7ee7

-- Sol generated from Probability/AdaptiveQSAllocation.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Why inverse-rate reallocation must lose, and why the floor clip is load-bearing

Experiment 559 (round-73 #2, `ADAPT-NULL-EQUALIZER / SKIP-FLIP-WINS`) measured an
adaptive quadratic sieve in which a cheap quadratic-residue dial predicts the
per-target relation *rate* well (Spearman `0.739`, oracle dial `0.778`,
`FB100 = 0.835`), and then reallocated sieve length in inverse proportion to the
predicted rate.  The reallocation **lost**: `-17.6%` total yield with a floor clip
in place, and a catastrophic `-146.7%` with the clip removed, while a
*concentrator* that pushes budget towards the high-rate targets gained `+8.6%`
and the realised oracle bound sat `+74.8%` above the baseline.

This file explains all four numbers as one exact theorem, at the level of the
allocation model itself: **no calibration error is involved, the sign of the
inverse-rate policy is forced.**

The model.  A budget `B` of sieve length is split over targets `i ∈ s` with
positive relation rates `r i` (relations per unit of sieve length); an allocation
`ℓ` yields `yieldOf s r ℓ = ∑ i ∈ s, r i * ℓ i`.

Main results.

* `card_sq_le_sum_mul_sum_inv`, `card_sq_lt_sum_mul_sum_inv` — the AM–HM core,
  with the strict form: `n² ≤ (∑ r)(∑ r⁻¹)`, strictly as soon as two rates differ.
  Proved by pairwise symmetrisation over `s ×ˢ s`, not quoted.
* `invRate_yield_le_uniform_yield` / `invRate_yield_lt_uniform_yield` — **the
  inverse-rate policy loses, always.**  Its yield is `B ·` harmonic mean of the
  rates, the uniform baseline is `B ·` arithmetic mean, and the loss is strict
  whenever the dial has anything to say (two rates differ).  So a dial with
  *perfect* calibration would still lose under this policy: the `-17.6%` is a
  property of the reallocation rule, not of the predictor.
* `clipYield_eq`, `clipYield_mono`, `clipYield_strictMono` — **the floor clip is
  load-bearing and monotonically so.**  Interpolating the clipped policy
  `ℓ i = f + (B - n f) (r i)⁻¹ / ∑ r⁻¹` in the floor `f`, the yield is affine and
  *strictly increasing* in `f`; `f = 0` is the unclipped policy and `f = B / n`
  is the uniform baseline.  Removing the clip is exactly moving down this line,
  which is why unclipped is worse than clipped and clipped is worse than uniform.
* `concentrator_yield_ge_uniform_yield` — pushing the whole budget onto a
  maximal-rate target beats uniform: the correct sign is the opposite one.
* `yield_le_budget_mul_sup` — the realised oracle bound: *every* admissible
  allocation is capped by `B ·` (max rate), so the measured `+74.8%` headroom is
  bounded by the rate spread and by nothing else.
* `oracle_gap_eq_budget_mul_sup_sub_mean` — the headroom of the uniform baseline
  is exactly `B (max r - mean r)`.
-/

open Probability.AdaptiveQS

open Finset

variable {ι : Type*}

/-! ## The allocation model -/





/-! ## The AM–HM core, proved by pairwise symmetrisation -/

private lemma two_le_ratio_add_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (2 : ℝ) ≤ x * y⁻¹ + y * x⁻¹ := by
  rw [← sub_nonneg]
  have h : x * y⁻¹ + y * x⁻¹ - 2 = (x - y) ^ 2 / (x * y) := by
    field_simp; ring
  rw [h]; positivity

private lemma two_lt_ratio_add_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) :
    (2 : ℝ) < x * y⁻¹ + y * x⁻¹ := by
  rw [← sub_pos]
  have h : x * y⁻¹ + y * x⁻¹ - 2 = (x - y) ^ 2 / (x * y) := by
    field_simp; ring
  rw [h]
  have h1 : (0:ℝ) < (x - y) ^ 2 := by
    have : x - y ≠ 0 := sub_ne_zero.mpr hne
    positivity
  exact div_pos h1 (mul_pos hx hy)

private lemma prod_sum_eq (s : Finset ι) (r : ι → ℝ) :
    (∑ i ∈ s, r i) * (∑ i ∈ s, (r i)⁻¹) = ∑ p ∈ s ×ˢ s, r p.1 * (r p.2)⁻¹ := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']

private lemma prod_sum_eq' (s : Finset ι) (r : ι → ℝ) :
    (∑ i ∈ s, r i) * (∑ i ∈ s, (r i)⁻¹) = ∑ p ∈ s ×ˢ s, r p.2 * (r p.1)⁻¹ := by
  rw [mul_comm, Finset.sum_mul_sum, ← Finset.sum_product']
  exact Finset.sum_congr rfl (fun p _ => mul_comm _ _)

private lemma two_mul_prod_sum (s : Finset ι) (r : ι → ℝ) :
    2 * ((∑ i ∈ s, r i) * (∑ i ∈ s, (r i)⁻¹))
      = ∑ p ∈ s ×ˢ s, (r p.1 * (r p.2)⁻¹ + r p.2 * (r p.1)⁻¹) := by
  rw [Finset.sum_add_distrib, ← prod_sum_eq, ← prod_sum_eq']
  ring



/-! ## The yields of the two policies -/






/-! ## The floor clip is load-bearing -/






/-! ## The concentrator and the oracle bound -/







open Probability.AdaptiveQS in
theorem solution(s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i)
    {a b : ι} (ha : a ∈ s) (hb : b ∈ s) (hab : r a ≠ r b) :
    (s.card : ℝ) ^ 2 < (∑ i ∈ s, r i) * (∑ i ∈ s, (r i)⁻¹) := by
  have hsum : ∑ p ∈ s ×ˢ s, (2 : ℝ)
      < ∑ p ∈ s ×ˢ s, (r p.1 * (r p.2)⁻¹ + r p.2 * (r p.1)⁻¹) := by
    refine Finset.sum_lt_sum ?_ ?_
    · intro p hp
      rw [Finset.mem_product] at hp
      exact two_le_ratio_add_ratio (hr _ hp.1) (hr _ hp.2)
    · refine ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, ?_⟩
      exact two_lt_ratio_add_ratio (hr _ ha) (hr _ hb) hab
  rw [← two_mul_prod_sum] at hsum
  simp only [Finset.sum_const, Finset.card_product, nsmul_eq_mul] at hsum
  push_cast at hsum
  nlinarith [hsum]
