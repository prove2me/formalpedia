-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdos_partition_limit_exists_of_alignment
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.erdos_partition_limit_exists_of_alignment
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T19:58:12.48374+00:00
-- url     : https://prove2.me/theorems/3427101a-fe66-456a-8c4c-a64739953bbc
-- title:
--   A conditional partition-limit reduction from renewal alignment
-- statement:
--   Let $u_n=n\,\texttt{part}(n)\exp(-C\sqrt n)$, with the source partition count and $C=\pi\sqrt{2/3}$. The source kernel, rank and killed hit-value constructions are those defined below. Assume `ErdosAlignment J` for all sufficiently large $J$. This means a single $0<\delta\le1$ at each such cutoff works for every natural step count $m$ and every $\varepsilon>0$, after increasing the rank threshold, so that the two killed-kernel $m$-step rows have overlap at least $1-(1-\delta)^m-\varepsilon$. Then $$\exists a>0,\quad u_n\longrightarrow a.$$ The full finite-slice overlap predicate is given below. Its production is a carried premise.
--
--   The local source models, scales or predicates are defined exactly by:
--
--   ```lean
--   def ErdosAlignment (J : ℕ) : Prop :=
--     ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
--       ∀ (m : ℕ) (ε : ℝ), 0 < ε → ∃ R₀ : ℕ, ∀ i j, R₀ ≤ rnk i → R₀ ≤ rnk j →
--         1 - (1 - δ) ^ m - ε ≤ ∑ k ∈ Finset.range (max i j + 1),
--             min (KPowK m (killedKer Pker rnk J) i k) (KPowK m (killedKer Pker rnk J) j k)
--   ```
--
--   This conditional reduction carries the following complete literal source contract:
--
--   ```lean
--   theorem erdos_partition_limit_exists_of_alignment
--       (ha : ∀ᶠ J : ℕ in atTop, ErdosAlignment J) :
--       ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/ErdosAlignConnect.lean#L31. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KilledHarmonic
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KilledKernelPow
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosAlignConnect
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin: the renewal-alignment connection to `erdos_partition_limit_exists`

The correct (satisfiable) Hardy–Ramanujan reduction.  Instantiates `tendsto_of_renewal_alignment` for the
concrete killed Erdős kernel: if the **renewal-alignment** holds for cofinitely many cutoffs `J` — the
`m`-step terminal laws of any two high-rank starts overlap by `≥ 1 − (1−δ)^m − ε` — then the normalized
partition sequence `u` converges to a positive limit.  Unlike the all-pairs single-step overlap (which is
false for far-rank pairs), the alignment input is genuinely satisfiable: two descending chains synchronize
at the shared lower rank levels they both pass through.  Opus-authored.
-/

open Filter Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.erdos_partition_limit_exists_of_alignment
    (ha : ∀ᶠ J : ℕ in atTop, ErdosAlignment J) :
    ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a) := by sorry
