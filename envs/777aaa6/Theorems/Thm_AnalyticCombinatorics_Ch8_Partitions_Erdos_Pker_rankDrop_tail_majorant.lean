-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_Pker_rankDrop_tail_majorant
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.Pker_rankDrop_tail_majorant
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T18:41:32.753347+00:00
-- url     : https://prove2.me/theorems/2cafe76e-8a82-400a-9156-6b68bedf5e25
-- title:
--   Supporting lemma: Pker rankDrop tail majorant
-- statement:
--   **T2.1 tail majorant (engine input).**  The rank-drop tail beyond `A` is uniformly (eventually in
--   `v`) dominated by `C₀·(A+1)·e^{−γA}` with `γ = C/60 > 0`.  An upper bound on the floor-rank drop is
--   unaffected by the documented `frac(3√v)` oscillation: a drop `> A` forces a jump `> (A/3)√v`, whose
--   `erdosWeight`-mass is exponentially small in `A` (bulk via the banked block majorants; the `2m > v`
--   half via `right_half_kernel_sum_le` + the poly-beats-exp slack `v³ ≤ e^{(C/20)√v}`; for `A ≥ 3√v` the
--   far window is empty).
--
--   The full literal source contract is:
--
--   ```lean
--   theorem Pker_rankDrop_tail_majorant :
--       ∃ (γ : ℝ) (C₀ : ℝ), 0 < γ ∧ ∀ᶠ v : ℕ in atTop, ∀ A : ℕ,
--           (∑ d ∈ (Finset.range v).filter (A < ·), rankDropKer v d)
--             ≤ C₀ * ((A : ℝ) + 1) * Real.exp (-γ * (A : ℝ))
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/RankDropKer.lean#L335. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RankDropKer
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

open Filter Topology BigOperators

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.Pker_rankDrop_tail_majorant :
    ∃ (γ : ℝ) (C₀ : ℝ), 0 < γ ∧ ∀ᶠ v : ℕ in atTop, ∀ A : ℕ,
        (∑ d ∈ (Finset.range v).filter (A < ·), rankDropKer v d)
          ≤ C₀ * ((A : ℝ) + 1) * Real.exp (-γ * (A : ℝ)) := by sorry
