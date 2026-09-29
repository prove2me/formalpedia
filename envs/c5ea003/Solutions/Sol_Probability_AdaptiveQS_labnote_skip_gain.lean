-- Prove2me | solution 1 for Probability.AdaptiveQS.labnote_skip_gain
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:34:16.23009+00:00
-- url     : https://prove2.me/submissions/9af8df21-d0fa-42d5-ad57-a2688b44e356

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
theorem solution:
    throughput Finset.univ labRate < throughput ({1, 2} : Finset (Fin 3)) labRate := by
  have h1 : ∑ i ∈ (Finset.univ : Finset (Fin 3)), labRate i = 8 := by
    simp [Fin.sum_univ_three, labRate]
    norm_num
  have h2 : ∑ i ∈ ({1, 2} : Finset (Fin 3)), labRate i = 7 := by
    rw [Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)]
    simp [labRate]
    norm_num
  have hc1 : ((Finset.univ : Finset (Fin 3)).card : ℝ) = 3 := by simp
  have hc2n : (({1, 2} : Finset (Fin 3)).card) = 2 := by decide
  have hc2 : ((({1, 2} : Finset (Fin 3)).card : ℝ)) = 2 := by rw [hc2n]; norm_num
  rw [throughput, throughput, h1, h2, hc1, hc2]
  norm_num
