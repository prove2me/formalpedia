-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_FKPartitionHitting
-- name    : AnalyticCombinatorics_Ch8_Partitions_FKPartitionHitting
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:46:57.656766+00:00
-- url     : https://prove2.me/theorems/56cae518-268e-4cce-9e8a-5c64ac379c44
-- title:
--   F K Partition Hitting
-- statement:
--   The source-linked mathematical setting supplies the finite-kernel, rank, moment, renewal or sequence models used by the exact support contracts in this group. The literal model declarations, where catalogued below, retain their source parameters and assumptions. Definition prose must be refined against the actual complete compiler-derived owner before an upload payload is prepared.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/FKPartitionHitting.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ITERCoupling
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

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)

/-- The FK drop set where one departure survival factor is at most `1 - δ`. -/
def dropSet (δ : ℝ) (xy : α × α) : Prop :=
  δ ≤ cmass P rnk W xy.1 xy.2

noncomputable instance dropSet_decidable (δ : ℝ) : DecidablePred (dropSet P rnk W δ) :=
  Classical.decPred _

variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)


end AnalyticCombinatorics.Ch8.Partitions.Erdos


