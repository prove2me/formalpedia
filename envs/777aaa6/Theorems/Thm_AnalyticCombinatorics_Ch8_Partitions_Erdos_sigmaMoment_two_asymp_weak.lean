-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_sigmaMoment_two_asymp_weak
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_two_asymp_weak
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:18:06.69831+00:00
-- url     : https://prove2.me/theorems/bfad74b3-d1eb-44b4-9a4f-ab0ea43ab699
-- title:
--   M₂ weak asymptotics
-- statement:
--   **`M₂` weak asymptotics**.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem sigmaMoment_two_asymp_weak {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
--       |sigmaMoment 2 t - 6 * (Real.pi ^ 2 / 6) / t ^ 4|
--         ≤ (3600 * 2 ^ 3 + (6 / (1 - Real.exp (-1)) ^ 4) * (Nat.factorial 2) * 4 ^ 3 + 2 * 6)
--             / t ^ 3
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MassRateMomentTwoAsymp.lean#L107. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Mass-rate campaign: `M₂` weak asymptotics

`|M₂(t) − 6(π²/6)/t⁴| ≤ K/t³` on `0 < t ≤ 1`.  Split `M₂ = Σ'_{k} k²·boseKernel3(tk)` via
`boseKernel3 z = 6/z⁴ + reg3(z)`: singular part sums (Basel) to `6(π²/6)/t⁴`, remainder
`Σ'_k k²·reg3(tk)` bounded by the weighted-decay keystone (`j=2`, `Cf=3600`, `Df=6`).  Opus-authored.
-/

set_option maxHeartbeats 1000000

open Filter
open scoped Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_two_asymp_weak {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    |sigmaMoment 2 t - 6 * (Real.pi ^ 2 / 6) / t ^ 4|
      ≤ (3600 * 2 ^ 3 + (6 / (1 - Real.exp (-1)) ^ 4) * (Nat.factorial 2) * 4 ^ 3 + 2 * 6)
          / t ^ 3 := by sorry
