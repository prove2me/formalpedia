-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosRenewalConnectMultiB
-- name    : AnalyticCombinatorics_Ch8_Partitions_ErdosRenewalConnectMultiB
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T19:56:56.418401+00:00
-- url     : https://prove2.me/theorems/29c5051c-a2ff-4f08-ae0b-db519c9adbde
-- title:
--   Erdos Renewal Connect Multi B
-- statement:
--   The source mathematical objects and operations are specified by the following definitions.
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
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/ErdosRenewalConnectMultiB.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KilledHarmonic
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KilledKernelPow
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
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

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The **multi-scale Doeblin walls** at cutoff `J`: Skolemized overlaps `δ_B > 0` on the band
`{rnk ≥ R−B}` and escape masses `≤ ε_B` below it (for the `L_B`-step killed kernel), with
`ε_B / δ_B → 0`. -/
def DoeblinWallsMultiB (J : ℕ) : Prop :=
  ∃ (δ ε : ℕ → ℝ) (L R₀ : ℕ → ℕ),
    (∀ B, 0 < δ B) ∧ (∀ B, δ B ≤ 1) ∧ (∀ B, 0 ≤ ε B) ∧
    Tendsto (fun B => ε B / δ B) atTop (𝓝 0) ∧
    (∀ B R, R₀ B ≤ R → ∀ i j, R ≤ rnk i → R ≤ rnk j →
       δ B ≤ ∑ k ∈ (Finset.range (max i j + 1)).filter (fun k => R - B ≤ rnk k),
              min (KPowK (L B) (killedKer Pker rnk J) i k)
                  (KPowK (L B) (killedKer Pker rnk J) j k)) ∧
    (∀ B R, R₀ B ≤ R → ∀ i, R ≤ rnk i →
       ∑ k ∈ (Finset.range (i + 1)).filter (fun k => ¬ (R - B ≤ rnk k)),
              KPowK (L B) (killedKer Pker rnk J) i k ≤ ε B)

end AnalyticCombinatorics.Ch8.Partitions.Erdos


