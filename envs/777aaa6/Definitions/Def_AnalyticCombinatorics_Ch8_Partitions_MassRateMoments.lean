-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
-- name    : AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:11:48.512199+00:00
-- url     : https://prove2.me/theorems/4f4df37a-818f-465a-9a57-12ab760f3b4d
-- title:
--   Mass Rate Moments mathematical objects
-- statement:
--   Exponentially damped divisor moments and the constant massLam=C/2 encode the kernel-mass expansion. The Bose kernel is exp(-x)/(1-exp(-x))^2, and boseReg0 is its difference from1/x^2 with the source real-division convention; no replacement value at x=0 is inserted.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MassRateMoments.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Mass-rate campaign: Lambert moments — definitions and the central cancellation (R8)

The critical-path brick `|kernelMass n − 1| = O(1/n)` goes through smoothed Lambert
moments `M_r(t) = Σ_m m^r σ(m) e^{−tm}` (NOT a refined pointwise summatory, which cannot
have an `o(x)` secondary at integers because of the `σ(n)` jumps).  This file banks the
definitions, the saddle parameter `λ = C/2` with `λ² = π²/6`, the Bose kernel with its
regularization, and the central algebraic cancellation of the `n^{−1/2}` coefficients:

  `−1/(2λ) + 2Z/λ³ − (C/8)·6Z/λ⁴ = 0`  (`Z = λ²`, `C = 2λ`).

Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The `r`-th Lambert moment of the divisor function: `Σ_m m^r σ(m) e^{−tm}`. -/
noncomputable def sigmaMoment (r : ℕ) (t : ℝ) : ℝ :=
  ∑' m : ℕ, if m = 0 then 0
    else (m : ℝ) ^ r * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))

/-- The saddle parameter `λ = C/2`. -/
noncomputable def massLam : ℝ := C / 2

end AnalyticCombinatorics.Ch8.Partitions.Erdos


