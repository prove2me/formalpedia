-- Prove2me | Theorems.Thm_Probability_AdaptiveQS_sum_le_of_bounded_exceptions
-- name    : Probability.AdaptiveQS.sum_le_of_bounded_exceptions
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:54:58.816823+00:00
-- url     : https://prove2.me/theorems/d0a8e7fa-aef9-4124-b558-4c0cbc1bbc72
-- title:
--   If every pair `(j, i) ∈ D ×ˢ K` outside an exceptional set `E` satisfies `r j ≤ r i`,
-- statement:
--   If every pair `(j, i) ∈ D ×ˢ K` outside an exceptional set `E` satisfies `r j ≤ r i`,
--   and all rates lie in `[0, M]`, then the retention beats the work fraction up to the
--   linear penalty `M |E|`.
--
--   ```lean
--   theorem Probability.AdaptiveQS.sum_le_of_bounded_exceptions{s K D : Finset ι} {r : ι → ℝ} {M : ℝ}
--       (hunion : K ∪ D = s) (hdisj : Disjoint K D) (hM : 0 ≤ M)
--       (hnonneg : ∀ i ∈ s, 0 ≤ r i) (hle : ∀ i ∈ s, r i ≤ M)
--       (E : Finset (ι × ι))
--       (hE : ∀ p ∈ D ×ˢ K, p ∉ E → r p.1 ≤ r p.2) :
--       (K.card : ℝ) * (∑ i ∈ s, r i) ≤ (s.card : ℝ) * (∑ i ∈ K, r i) + M * E.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AdaptiveQSDiscordance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AdaptiveQSDiscordance.lean#L55

-- Thm stub generated from Probability/AdaptiveQSDiscordance.lean
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

theorem Probability.AdaptiveQS.sum_le_of_bounded_exceptions{s K D : Finset ι} {r : ι → ℝ} {M : ℝ}
    (hunion : K ∪ D = s) (hdisj : Disjoint K D) (hM : 0 ≤ M)
    (hnonneg : ∀ i ∈ s, 0 ≤ r i) (hle : ∀ i ∈ s, r i ≤ M)
    (E : Finset (ι × ι))
    (hE : ∀ p ∈ D ×ˢ K, p ∉ E → r p.1 ≤ r p.2) :
    (K.card : ℝ) * (∑ i ∈ s, r i) ≤ (s.card : ℝ) * (∑ i ∈ K, r i) + M * E.card := by sorry
