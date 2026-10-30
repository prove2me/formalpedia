-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_boseReg0Deriv_bdd_near_zero
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.boseReg0Deriv_bdd_near_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:17:33.161151+00:00
-- url     : https://prove2.me/theorems/312eb1a8-ef55-4bcd-8388-a04aae6adb53
-- title:
--   Near-zero derivative bound
-- statement:
--   **Near-zero derivative bound** (R10 brick 16): `|boseReg0′| ≤ 32` on `(0,1]`.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma boseReg0Deriv_bdd_near_zero {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
--       |boseReg0Deriv x| ≤ 32
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MassRateDerivZero.lean#L35. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateDeriv
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Mass-rate campaign: near-zero derivative bound (R10 brick 16)

`|boseReg0′| ≤ 32` on `(0,1]`, via the hand-computed degree-6 cancellation: with
`y = eˣ−1 = P + δ`, `P = x + x²/2 + x³/6`, `|δ| ≤ x⁴`,

  `2y³ − x³(2+3y+y²) = (−x⁶/4 − x⁷/6 − x⁸/12 − x⁹/54)
      + δ(6x² + 3x³ + 3x⁴/2 − x⁶/6) + δ²(6P − x³) + 2δ³`

(a `ring`-checkable identity), each piece `≤ 11x⁶` in absolute value, denominator
`x³y³ ≥ x⁶`.  Opus-authored.
-/

set_option maxHeartbeats 1000000

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.boseReg0Deriv_bdd_near_zero {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    |boseReg0Deriv x| ≤ 32 := by sorry
