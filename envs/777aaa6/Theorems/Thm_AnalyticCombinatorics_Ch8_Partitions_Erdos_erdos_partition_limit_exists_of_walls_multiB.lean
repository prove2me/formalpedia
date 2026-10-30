-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdos_partition_limit_exists_of_walls_multiB
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.erdos_partition_limit_exists_of_walls_multiB
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T19:57:49.027777+00:00
-- url     : https://prove2.me/theorems/091ac487-5c49-461f-bedd-6bf0a39b8af6
-- title:
--   A conditional partition-limit reduction from multiscale Doeblin walls
-- statement:
--   Let $u_n=n\,\texttt{part}(n)\exp(-C\sqrt n)$, with the source partition count and $C=\pi\sqrt{2/3}$. The source kernel, rank and killed hit-value constructions are those defined below. Assume `DoeblinWallsMultiB J` for all sufficiently large cutoffs $J$. At each such cutoff this includes functions $\delta_B,\varepsilon_B,L_B,R_{0,B}$ with $0<\delta_B\le1$, $\varepsilon_B\ge0$, $\varepsilon_B/\delta_B\to0$, a uniform $L_B$-step overlap lower bound inside the rank wall, and an escape-mass upper bound $\varepsilon_B$ outside it. With all quantifiers and finite slices as defined below, $$\exists a>0,\quad u_n\longrightarrow a.$$ No wall family is constructed by this implication.
--
--   The local source models, scales or predicates are defined exactly by:
--
--   ```lean
--   def DoeblinWallsMultiB (J : ℕ) : Prop :=
--     ∃ (δ ε : ℕ → ℝ) (L R₀ : ℕ → ℕ),
--       (∀ B, 0 < δ B) ∧ (∀ B, δ B ≤ 1) ∧ (∀ B, 0 ≤ ε B) ∧
--       Tendsto (fun B => ε B / δ B) atTop (𝓝 0) ∧
--       (∀ B R, R₀ B ≤ R → ∀ i j, R ≤ rnk i → R ≤ rnk j →
--          δ B ≤ ∑ k ∈ (Finset.range (max i j + 1)).filter (fun k => R - B ≤ rnk k),
--                 min (KPowK (L B) (killedKer Pker rnk J) i k)
--                     (KPowK (L B) (killedKer Pker rnk J) j k)) ∧
--       (∀ B R, R₀ B ≤ R → ∀ i, R ≤ rnk i →
--          ∑ k ∈ (Finset.range (i + 1)).filter (fun k => ¬ (R - B ≤ rnk k)),
--                 KPowK (L B) (killedKer Pker rnk J) i k ≤ ε B)
--   ```
--
--   This conditional reduction carries the following complete literal source contract:
--
--   ```lean
--   theorem erdos_partition_limit_exists_of_walls_multiB
--       (hwalls : ∀ᶠ J : ℕ in atTop, DoeblinWallsMultiB J) :
--       ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/ErdosRenewalConnectMultiB.lean#L37. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KilledHarmonic
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KilledKernelPow
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosRenewalConnectMultiB
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin: the multi-scale connection to `erdos_partition_limit_exists`

The correct (multi-scale) Hardy–Ramanujan reduction for the Erdős kernel.  The walls are B-indexed:
for each band width `B` a finite-time overlap `δ_B > 0` on `{rnk ≥ R−B}` and an escape mass `≤ ε_B`
below it, with `ε_B / δ_B → 0`.  (Unlike the fixed-band escape-split version, the escape here need not
vanish at any single `B`; the *family* with `ε_B/δ_B → 0` drives the tail oscillation to `0`.)  This is
the satisfiable form of `DoeblinWalls`.  Opus-authored.
-/

open Filter Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.erdos_partition_limit_exists_of_walls_multiB
    (hwalls : ∀ᶠ J : ℕ in atTop, DoeblinWallsMultiB J) :
    ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a) := by sorry
