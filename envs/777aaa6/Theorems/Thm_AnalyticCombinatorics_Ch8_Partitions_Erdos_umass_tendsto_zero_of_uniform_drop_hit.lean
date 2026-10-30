-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_umass_tendsto_zero_of_uniform_drop_hit
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.umass_tendsto_zero_of_uniform_drop_hit
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:49:54.360762+00:00
-- url     : https://prove2.me/theorems/2209fbca-2728-4b6c-b7de-aa6d930bf3f9
-- title:
--   Conditional coalescence from uniform drop-set hitting
-- statement:
--   Carries a uniform drop-set hitting lower bound for the free residual chain. It does not prove that bound for frozen-apart starts.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem umass_tendsto_zero_of_uniform_drop_hit (i j : α)
--       (δ p0 : ℝ) (hδ : 0 < δ) (hp0 : 0 < p0)
--       (M : ℕ) (hM : 0 < M)
--       (hhit :
--         ∀ xy, p0 ≤ hitProb (KhatResPair P rnk W) (dropSet P rnk W δ) M xy) :
--       Tendsto (fun t => umass P rnk W i j t) atTop (𝓝 0)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/FKPartitionHitting.lean#L39. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_FKHittingBridge
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ITERCoupling
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_FKPartitionHitting
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KhatRes
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Partition FK hitting bridge

This file packages the concrete drop-set interface for the partition residual
coupling: a uniform free-`KhatRes` hitting lower bound for
`{xy | δ ≤ cmass xy}` implies `umass → 0`.
-/

open Filter Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)

variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
include hPnn hPmass

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.umass_tendsto_zero_of_uniform_drop_hit (i j : α)
    (δ p0 : ℝ) (hδ : 0 < δ) (hp0 : 0 < p0)
    (M : ℕ) (hM : 0 < M)
    (hhit :
      ∀ xy, p0 ≤ hitProb (KhatResPair P rnk W) (dropSet P rnk W δ) M xy) :
    Tendsto (fun t => umass P rnk W i j t) atTop (𝓝 0) := by sorry
