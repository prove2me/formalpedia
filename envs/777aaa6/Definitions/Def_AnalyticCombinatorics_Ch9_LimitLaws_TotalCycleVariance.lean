-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_TotalCycleVariance
-- name    : AnalyticCombinatorics_Ch9_LimitLaws_TotalCycleVariance
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T15:49:27.070584+00:00
-- url     : https://prove2.me/theorems/737a2da9-43b7-4839-ba32-d8568b1a5334
-- title:
--   Exact variance of all cycles of a uniform permutation
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   noncomputable def cycleH1 (n : ℕ) : ℝ :=
--     ∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹
--   ```
--
--   ```lean
--   noncomputable def cycleH2 (n : ℕ) : ℝ :=
--     ∑ r ∈ Finset.Icc 1 n, ((r : ℝ)⁻¹) ^ 2
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/TotalCycleVariance.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Exact variance of the total number of cycles in a uniform random permutation

The Goncharov–Kolchin companion to the cycle-count CLT: for `K_n` the total number of cycles of a
uniform random permutation of `[n]`,

  `E[K_n] = H_n`,   `Var(K_n) = H_n − H_n^{(2)}`,

where `H_n = ∑_{r=1}^n 1/r` and `H_n^{(2)} = ∑_{r=1}^n 1/r²`.

`TotalCycleSecondMoment` already reduces the variance to `H_n + cycleFitPairSum n − H_n²`.  This file
supplies the one remaining finite identity `cycleFitPairSum n = H_n² − H_n^{(2)}` (antidiagonal split
`1/(r(n+1−r)) = (1/r + 1/(n+1−r))/(n+1)` plus the reflection `r ↦ n+1−r`), giving the exact variance.
-/

noncomputable section

open Filter Asymptotics
open scoped BigOperators Topology

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS

/-- First harmonic sum `H_n = ∑_{r=1}^n 1/r`. -/
noncomputable def cycleH1 (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹

/-- Second harmonic sum `H_n^{(2)} = ∑_{r=1}^n 1/r²`. -/
noncomputable def cycleH2 (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 n, ((r : ℝ)⁻¹) ^ 2

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics


