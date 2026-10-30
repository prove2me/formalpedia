-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_ExpectedCycles
-- name    : AnalyticCombinatorics_Ch9_LimitLaws_ExpectedCycles
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T15:54:30.106885+00:00
-- url     : https://prove2.me/theorems/756f2249-db26-469a-99ef-5c5d435cf059
-- title:
--   Expected Cycles
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def totalCycleCount (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
--     ∑ r ∈ Finset.Icc 1 n, rCycleCount n r σ
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/ExpectedCycles.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_RCyclesPoisson
import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Expected number of cycles of a random permutation

The total number of cycles (orbits, including fixed points) of a permutation of `Fin n` is
`∑_{r=1}^{n} C_{n,r}`, where `C_{n,r} = rCycleCount n r` is the number of length-`r` cycles.
Summing the banked per-length means `E[C_{n,r}] = 1/r` (`rCycle_mean_eq_inv`) over `r = 1,…,n` by
linearity of expectation gives the classical identity

  `E[#cycles] = ∑_{r=1}^{n} 1/r = H_n`,

the `n`-th harmonic number.  (Asymptotically `H_n ∼ log n`, recovering the Goncharov result that a
uniform random permutation has about `log n` cycles.)

This is a genuine consequence of the factorial-moment machinery, not a Mathlib re-statement.
-/

noncomputable section

open Filter
open scoped BigOperators

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS

/-- The total number of cycles (orbits, including fixed points) of `σ`, as the sum over all possible
lengths `r = 1,…,n` of the number of length-`r` cycles. -/
def totalCycleCount (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  ∑ r ∈ Finset.Icc 1 n, rCycleCount n r σ


end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics


