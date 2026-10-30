-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_sigmaMoment_three_one_term
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_three_one_term
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:17:33.635814+00:00
-- url     : https://prove2.me/theorems/436ab788-ca26-499f-9e0f-d7bf99d1707b
-- title:
--   M₃ one-term asymptotic
-- statement:
--   **`M₃` one-term asymptotic** `|M₃(t) − 24(π²/6)/t⁵| ≤ K/t⁴` on `0 < t ≤ 1`.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem sigmaMoment_three_one_term {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
--       |sigmaMoment 3 t - 24 * (Real.pi ^ 2 / 6) / t ^ 5|
--         ≤ (2645 * 2 ^ 4 + (24 / (1 - Real.exp (-1)) ^ 5) * (Nat.factorial 3) * 4 ^ 4 + 2 * 24)
--             / t ^ 4
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MassRateMomentThreeAsymp.lean#L110. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Mass-rate campaign: `M₃` one-term asymptotics

`|M₃(t) − 24(π²/6)/t⁵| ≤ K/t⁴` on `0 < t ≤ 1`.  Split `M₃ = Σ'_{k} k³·boseKernel4(tk)` via
`boseKernel4 z = 24/z⁵ + reg4(z)`: singular part sums (Basel) to `24(π²/6)/t⁵`, remainder
`Σ'_k k³·reg4(tk)` bounded by the weighted-decay keystone (`j=3`, `Cf=2645`, `Df=24`).
Mirror of `MassRateMomentTwoAsymp`, powers shifted +1.  Opus-authored.
-/

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_three_one_term {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    |sigmaMoment 3 t - 24 * (Real.pi ^ 2 / 6) / t ^ 5|
      ≤ (2645 * 2 ^ 4 + (24 / (1 - Real.exp (-1)) ^ 5) * (Nat.factorial 3) * 4 ^ 4 + 2 * 24)
          / t ^ 4 := by sorry
