-- Prove2me | solution 1 for Probability.AdaptiveQS.sum_le_of_separated_slack
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:26:33.087339+00:00
-- url     : https://prove2.me/submissions/bf92ad31-6f14-4370-b7cf-a4f0ea2d7592

-- Sol generated from Probability/AdaptiveQSSkipFlip.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSSkipFlip
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Skip-flip wins, and the quadratic-residue null equaliser

Companion to `Probability.AdaptiveQSAllocation`.  That file shows that spending a
*fixed* budget in inverse proportion to a predicted rate must lose.  Experiment 559
then flipped the deployment: instead of reallocating sieve length, use the same
dial to **skip** the worst targets (`θ = q20` skipped `28.3%` of the work while
retaining `89.5%` of the relations, a `+28.9%` throughput gain), and defer the hard
tail (`40/400` targets that no amount of sieving reaches).

This file proves that the flip is not a lucky calibration but a theorem, in three
layers.

1. **Separation ⇒ retention beats work fraction.**  `sum_le_of_separated_slack` is
   the general engine: if every kept target beats every skipped target up to a slack
   `c`, then `|K| · (total yield) ≤ |s| · (kept yield) + c |K| |D|`.  With `c = 0`
   (`retention_ge_work_fraction`) this says exactly `retention ≥ work fraction`, i.e.
   the throughput ratio is `≥ 1`; `skip_throughput_ge` and `skip_throughput_gt` state
   it as a mean comparison, the latter strictly.

2. **An imperfect dial still wins, quantitatively.**  `approx_dial_retention` runs
   the same engine with `c = 2ε` for a dial that is only `ε`-accurate — the measured
   Spearman `0.739 < 1` costs at most a `2ε` degradation term, and
   `approx_dial_threshold_gain` gives the explicit condition on `ε` under which the
   skip still wins.  This is the robustness statement the deployment needs.

3. **The null equaliser is exact arithmetic, not statistics.**  A prime `p` for which
   `N` is a quadratic *non*-residue divides **no** value `x² - N`
   (`nonresidue_not_dvd_qsValue`), so its sieve hit rate is identically zero
   (`hitRate_eq_zero_of_nonresidue`) — the hard tail is unreachable by construction.
   `qs_null_equalizer` then says the yield of *any* allocation is unchanged by
   deleting the null targets, and `transfer_from_null_lt` says that moving any
   positive amount of budget off a null target onto a live one strictly increases the
   yield.  Deferral, not deeper sieving, is the instrument.
-/

open Probability.AdaptiveQS

open Finset

variable {ι : Type*} [DecidableEq ι]

/-! ## The separation engine -/




/-! ## The deployment flip: threshold skipping -/












/-! ## An imperfect dial: the quantitative flip -/



/-! ## The quadratic-residue null equaliser -/










open Probability.AdaptiveQS in
theorem solution{s K D : Finset ι} {r : ι → ℝ} {c : ℝ}
    (hunion : K ∪ D = s) (hdisj : Disjoint K D)
    (hsep : ∀ i ∈ K, ∀ j ∈ D, r j ≤ r i + c) :
    (K.card : ℝ) * (∑ i ∈ s, r i)
      ≤ (s.card : ℝ) * (∑ i ∈ K, r i) + c * K.card * D.card := by
  have hsplit : ∑ i ∈ s, r i = (∑ i ∈ K, r i) + ∑ j ∈ D, r j := by
    rw [← hunion, Finset.sum_union hdisj]
  have hcard : (s.card : ℝ) = (K.card : ℝ) + (D.card : ℝ) := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
    push_cast
    ring
  -- the cross bound `|K| ∑_D r ≤ |D| ∑_K r + c |K| |D|`
  have hcross : (K.card : ℝ) * (∑ j ∈ D, r j)
      ≤ (D.card : ℝ) * (∑ i ∈ K, r i) + c * K.card * D.card := by
    have hterm : ∀ p ∈ D ×ˢ K, r p.1 ≤ r p.2 + c := by
      intro p hp
      rw [Finset.mem_product] at hp
      exact hsep _ hp.2 _ hp.1
    have hsum : ∑ p ∈ D ×ˢ K, r p.1 ≤ ∑ p ∈ D ×ˢ K, (r p.2 + c) :=
      Finset.sum_le_sum hterm
    have hL : ∑ p ∈ D ×ˢ K, r p.1 = (K.card : ℝ) * ∑ j ∈ D, r j := by
      simp only [Finset.sum_product, Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.mul_sum]
    have hR : ∑ p ∈ D ×ˢ K, (r p.2 + c)
        = (D.card : ℝ) * (∑ i ∈ K, r i) + c * K.card * D.card := by
      simp only [Finset.sum_product, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.card_product]
      push_cast
      ring
    rw [hL, hR] at hsum
    exact hsum
  rw [hsplit, hcard]
  nlinarith [hcross]
