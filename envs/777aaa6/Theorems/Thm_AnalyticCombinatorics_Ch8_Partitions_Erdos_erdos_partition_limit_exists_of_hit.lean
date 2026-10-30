-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdos_partition_limit_exists_of_hit
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.erdos_partition_limit_exists_of_hit
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T18:54:56.340094+00:00
-- url     : https://prove2.me/theorems/d2a75d58-a90c-4675-9c34-2958bab3b4c9
-- title:
--   Supporting lemma: erdos partition limit exists of hit
-- statement:
--   **Convergence modulo Fact B.** If the harmonic hit values converge for cofinitely many cutoffs,
--   the normalized partition sequence `u` converges to a positive limit.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem erdos_partition_limit_exists_of_hit
--       (hhit : ∀ᶠ J : ℕ in atTop,
--           ∃ L : ℝ, Tendsto (fun n => hitVal Pker rnk J u n) atTop (𝓝 L)) :
--       ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/ErdosLimit.lean#L22. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RenewalHitPot
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
# R7 assembly: `erdos_partition_limit_exists` modulo the hard core (Fact B)

Instantiates the renewal spine to the partition kernel: with all Layer-1 kernel facts proven
(`Pker_mass`, `dres_block_bound`, `hP_leave_partition`) plus the well-founded `hitVal`/`potVal`,
`rec_iter_bound` + `pot_le_block_sum_of_leave` + `block_sum_le_tail` give the uniform
hit-approximation `|u n − hitVal_J n| ≤ (1/μ)·tail_J`, and the convergence engine
`tendsto_of_uniform_hit_approx` then yields convergence — *modulo* the single hard analytic
hypothesis (Fact B): for cofinitely many cutoffs `J`, the hit value `hitVal Pker rnk J u` converges.
Opus-authored.
-/

open Filter Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.erdos_partition_limit_exists_of_hit
    (hhit : ∀ᶠ J : ℕ in atTop,
        ∃ L : ℝ, Tendsto (fun n => hitVal Pker rnk J u n) atTop (𝓝 L)) :
    ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a) := by sorry
