-- Prove2me | solution 1 for Probability.AdaptiveQS.sum_le_of_bounded_exceptions
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:37:03.298292+00:00
-- url     : https://prove2.me/submissions/41b8dd94-bbf2-4ce6-afba-109f9a815f2b

-- Sol generated from Probability/AdaptiveQSDiscordance.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSDiscordance
import Definitions.Def_Probability_AdaptiveQSSkipFlip
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# From rank correlation to yield: a discordance budget for the skip-flip

Second cycle on experiment 559.  `Probability.AdaptiveQSSkipFlip` proves that a
*concordant* dial (one that never orders two targets backwards) always wins when it
is deployed as a skip rule.  The measured dial is **not** concordant: its Spearman
correlation against the realised yield is `0.739` (oracle dial `0.778`,
`FB100 0.835`), i.e. a positive but bounded number of ranking inversions.  The
question this file settles is the one the measurement actually poses:

> how much yield can a *bounded number of inversions* cost the skip rule?

The answer is a linear discordance budget.  Writing `Disc` for the set of ordered
pairs the dial gets backwards and `M` for the largest rate,

`|K| · (total yield) ≤ |s| · (kept yield) + M · |Disc|`,

so the retention deficit is at most `M |Disc| / (|s| · |K|)` per unit of work
(`throughput_le_of_discordance`).  With `Disc = ∅` this is exactly the concordant
theorem of the previous cycle (`retention_ge_work_fraction`), and the bound
degrades *linearly*, not catastrophically, in the number of inversions — which is
why a dial with Spearman well below `1` still retained `89.5%` of the relations
while skipping `28.3%` of the work.

Main results.

* `discordantPairs` — the inversion set of a dial against the true rate.
* `sum_le_of_bounded_exceptions` — the general engine: separation with an
  exceptional set of pairs, each of which can cost at most `M`.
* `retention_of_discordance` — the discordance budget for threshold skipping.
* `throughput_le_of_discordance` — the same bound in throughput (yield per unit of
  work) form.
* `retention_of_discordance_eq_concordant` — the bound collapses to the exact
  concordant statement when the inversion set is empty (consistency check).
* Lab notes: `labnote_invRate_loses`, `labnote_skip_gain`,
  `labnote_concentrator_gain` — a fully explicit three-target instance with the
  qualitative shape of the measured run (inverse-rate allocation loses ~34%,
  skipping the worst target retains `87.5%` of the yield for `66.7%` of the work,
  the concentrator gains).
-/

open Probability.AdaptiveQS

open Finset

variable {ι : Type*} [DecidableEq ι]

/-! ## Separation with a bounded set of exceptions -/


/-! ## The discordance budget -/





/-! ## Lab notes: an explicit three-target instance

The rates `(1, 2, 5)` on three targets reproduce the qualitative shape of the measured
run: the inverse-rate policy loses about a third of the yield, the concentrator gains,
and skipping the single worst target retains `87.5%` of the relations for `66.7%` of the
work (measured: `89.5%` for `71.7%`).  All three are decided by `norm_num`, not asserted.
-/






open Probability.AdaptiveQS in
theorem solution{s K D : Finset ι} {r : ι → ℝ} {M : ℝ}
    (hunion : K ∪ D = s) (hdisj : Disjoint K D) (hM : 0 ≤ M)
    (hnonneg : ∀ i ∈ s, 0 ≤ r i) (hle : ∀ i ∈ s, r i ≤ M)
    (E : Finset (ι × ι))
    (hE : ∀ p ∈ D ×ˢ K, p ∉ E → r p.1 ≤ r p.2) :
    (K.card : ℝ) * (∑ i ∈ s, r i) ≤ (s.card : ℝ) * (∑ i ∈ K, r i) + M * E.card := by
  have hKs : K ⊆ s := hunion ▸ Finset.subset_union_left
  have hDs : D ⊆ s := hunion ▸ Finset.subset_union_right
  have hsplit : ∑ i ∈ s, r i = (∑ i ∈ K, r i) + ∑ j ∈ D, r j := by
    rw [← hunion, Finset.sum_union hdisj]
  have hcard : (s.card : ℝ) = (K.card : ℝ) + (D.card : ℝ) := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
    push_cast
    ring
  -- pairwise bound with an indicator penalty
  have hterm : ∀ p ∈ D ×ˢ K, r p.1 - r p.2 ≤ if p ∈ E then M else 0 := by
    intro p hp
    rw [Finset.mem_product] at hp
    by_cases hpE : p ∈ E
    · simp only [hpE, if_true]
      have h1 : r p.1 ≤ M := hle _ (hDs hp.1)
      have h2 : 0 ≤ r p.2 := hnonneg _ (hKs hp.2)
      linarith
    · simp only [hpE, if_false]
      linarith [hE p (Finset.mem_product.mpr hp) hpE]
  have hsum : ∑ p ∈ D ×ˢ K, (r p.1 - r p.2) ≤ ∑ p ∈ D ×ˢ K, (if p ∈ E then M else 0) :=
    Finset.sum_le_sum hterm
  -- the penalty sum is at most `M |E|`
  have hpen : ∑ p ∈ D ×ˢ K, (if p ∈ E then M else 0) ≤ M * E.card := by
    have hMnn : 0 ≤ M := hM
    calc ∑ p ∈ D ×ˢ K, (if p ∈ E then M else 0)
        = ∑ p ∈ (D ×ˢ K).filter (fun p => p ∈ E), M := by
          rw [Finset.sum_filter]
      _ ≤ ∑ _p ∈ E, M := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hMnn)
          intro p hp
          rw [Finset.mem_filter] at hp
          exact hp.2
      _ = M * E.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- unfold the double sum
  have hL : ∑ p ∈ D ×ˢ K, (r p.1 - r p.2)
      = (K.card : ℝ) * (∑ j ∈ D, r j) - (D.card : ℝ) * ∑ i ∈ K, r i := by
    simp only [Finset.sum_product, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.mul_sum]
  rw [hL] at hsum
  rw [hsplit, hcard]
  nlinarith [hsum, hpen]
