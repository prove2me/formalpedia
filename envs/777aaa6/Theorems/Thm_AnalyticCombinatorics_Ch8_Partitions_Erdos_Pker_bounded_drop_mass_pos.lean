-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_Pker_bounded_drop_mass_pos
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.Pker_bounded_drop_mass_pos
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:32:25.727788+00:00
-- url     : https://prove2.me/theorems/8bf0e081-fb6e-4d7d-ae3d-02a8415d7a91
-- title:
--   Positive bounded rank-drop mass
-- statement:
--   Concrete positive bounded rank-drop mass only. The source explicitly does not supply cross-start first-entrance overlap or vanishing overshoot.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem Pker_bounded_drop_mass_pos :
--       ∃ μ : ℝ, 0 < μ ∧ ∀ᶠ n : ℕ in atTop,
--         μ ≤ ∑ k ∈ (Finset.range n).filter
--               (fun k => rnk n ≤ rnk k + 7 ∧ rnk k < rnk n), Pker n k
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/RankBandLocalLower.lean#L68. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# TASK 11, Step E (partial): the local bounded-rank-drop lower bound

The honest local kernel content available from the banked window mass: from a state `n`, a uniformly
positive `Pker`-mass (`≥ ν/2`) lands at a predecessor whose rank drops by a **bounded** amount
(at most `7`) — the window steps `m ∈ (√n, 2√n]` drop rank by `rnk n − rnk(n−m) ∈ [1, 7]`.  This is the
local-limit lower bound the entrance-overlap analysis needs *at the ceiling* (a state sitting just
above a band lands inside it with positive mass).

This does **not** by itself give the first-entrance *overlap between two different starts*, nor does it
kill the overshoot escape at fixed band width — those are the renewal-overshoot equidistribution
content.  It is the strongest fragment of Step E derivable from
the banked window mass, and is reusable for any renewal-coupling attempt.  Opus-authored.
-/

open Filter Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.Pker_bounded_drop_mass_pos :
    ∃ μ : ℝ, 0 < μ ∧ ∀ᶠ n : ℕ in atTop,
      μ ≤ ∑ k ∈ (Finset.range n).filter
            (fun k => rnk n ≤ rnk k + 7 ∧ rnk k < rnk n), Pker n k := by sorry
