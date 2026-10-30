-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RankDropKer
-- name    : AnalyticCombinatorics_Ch8_Partitions_RankDropKer
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T18:39:10.07658+00:00
-- url     : https://prove2.me/theorems/1e473973-a7f1-4052-a2de-e31c90326119
-- title:
--   Rank Drop Ker mathematical objects
-- statement:
--   The rank-drop kernel sums Pker over states having a prescribed rank decrement. A geometric-polynomial infinite sum provides the corresponding majorant constant.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/RankDropKer.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
import Mathlib

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Close end AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# T2.1 (honest restatement): the rank-drop kernel and its exponential tail majorant

The pointwise rank-drop *local limit* `rankDropKer v d → p d` is FALSE for the floor rank
`rnk v = ⌊3√v⌋` (the drop-`d` set is a `y`-window whose edges oscillate with `frac(3√v)`).  The engine, however, does not consume that limit; it consumes a
one-sided pair:

* an **exponential tail majorant** of the rank-drop, uniform in `v` (this file, `Pker_rankDrop_tail_majorant`);
* a **phase-uniform per-drop minorization** `rankDropKer v 1, rankDropKer v 2 ≥ η` (the genuinely
  new analytic input; see the gap doc).

This file builds the tail majorant.  An *upper* bound on the rank-drop is unaffected by the floor
oscillation: a rank drop exceeding `A` forces a *large jump* `m ≳ (A/3)√v`, whose `erdosWeight`-mass
is exponentially small in `A` (banked block-majorant machinery `left_half_tail_sum_le_block_majorants`
for the bulk `2m ≤ v` half, and `right_half_kernel_sum_le` for the `2m > v` half).

`rankDropKer` is the rank-drop law of the predecessor kernel `Pker`; it is exactly the pushforward of
`Pker v ·` under the rank-drop `k ↦ rnk v - rnk k`.

Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

/-- **Rank-drop kernel.**  `rankDropKer v d` is the `Pker`-probability that one predecessor step
from `v` drops the rank by exactly `d`: the mass of `Pker v ·` on `{k < v : rnk v − rnk k = d}`. -/
noncomputable def rankDropKer (v d : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range v).filter (fun k => rnk v - rnk k = d), Pker v k

end AnalyticCombinatorics.Ch8.Partitions.Erdos


