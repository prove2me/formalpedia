-- Prove2me | Definitions.Def_Probability_AdaptiveQSDiscordance
-- name    : Probability_AdaptiveQSDiscordance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:08:15.083558+00:00
-- url     : https://prove2.me/theorems/bfc90887-06e1-470f-ba69-37c2048b8b4e
-- title:
--   Aether Catalog definitions — Probability_AdaptiveQSDiscordance
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.AdaptiveQSDiscordance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/AdaptiveQSDiscordance.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
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

namespace Probability.AdaptiveQS

open Finset

variable {ι : Type*} [DecidableEq ι]

/-! ## Separation with a bounded set of exceptions -/


/-! ## The discordance budget -/

/-- The **inversion set** of a dial `d` against the true rate `r` on `s`: the ordered
pairs `(j, i)` on which the dial says `j` is worse but the rate says `j` is better.
Its cardinality is the unnormalised Kendall discordance count. -/
noncomputable def discordantPairs (s : Finset ι) (d r : ι → ℝ) : Finset (ι × ι) :=
  (s ×ˢ s).filter (fun p => d p.1 < d p.2 ∧ r p.2 < r p.1)




/-! ## Lab notes: an explicit three-target instance

The rates `(1, 2, 5)` on three targets reproduce the qualitative shape of the measured
run: the inverse-rate policy loses about a third of the yield, the concentrator gains,
and skipping the single worst target retains `87.5%` of the relations for `66.7%` of the
work (measured: `89.5%` for `71.7%`).  All three are decided by `norm_num`, not asserted.
-/

/-- The lab-note rate vector: three targets with rates `1, 2, 5`. -/
def labRate : Fin 3 → ℝ := ![1, 2, 5]




end Probability.AdaptiveQS


