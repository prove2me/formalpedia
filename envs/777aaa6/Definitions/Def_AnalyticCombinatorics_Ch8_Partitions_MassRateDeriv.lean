-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateDeriv
-- name    : AnalyticCombinatorics_Ch8_Partitions_MassRateDeriv
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:08:09.493008+00:00
-- url     : https://prove2.me/theorems/ca481450-1753-4971-9b49-9f2179e88fd4
-- title:
--   Mass Rate Deriv mathematical objects
-- statement:
--   The regularized Bose derivative is an explicitly defined real function, retaining its source treatment at the origin.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MassRateDeriv.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Mass-rate campaign: the boseReg0 derivative (R10 bricks 14, 15, 17)

`boseReg0′(x) = −eˣ(eˣ+1)/(eˣ−1)³ + 2/x³` on `(0,∞)`, with the tail bound
`|boseReg0′| ≤ 16e^{−x/2} + 2/x³` for `x ≥ 1`.  (The near-zero derivative bound —
brick 16 — needs the degree-6 cancellation certificate and is a separate brick.)
Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The closed form of `boseReg0′`. -/
noncomputable def boseReg0Deriv (x : ℝ) : ℝ :=
  -(Real.exp x * (Real.exp x + 1)) / (Real.exp x - 1) ^ 3 + 2 / x ^ 3

end AnalyticCombinatorics.Ch8.Partitions.Erdos


