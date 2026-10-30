-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch9_LimitLaws_RCyclesPoissonNS_totalCycleCount_variance_eq_harmonic_sub_harmonic2
-- name    : AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.totalCycleCount_variance_eq_harmonic_sub_harmonic2
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T15:58:09.396699+00:00
-- url     : https://prove2.me/theorems/9dc46370-c158-4b61-91d5-989750eb1a1b
-- title:
--   Exact variance of all cycles of a uniform permutation
-- statement:
--   For a uniform permutation $\sigma$ of $n$ labels, let $K(\sigma)$ count all cycles including fixed points. For every $n\in\mathbb N$, including zero, $$\mathbb E[K^2]-(\mathbb E K)^2=H_n-H_n^{(2)},\qquad H_n=\sum_{j=1}^n\frac1j,\quad H_n^{(2)}=\sum_{j=1}^n\frac1{j^2}.$$ Expectations are the source finite uniform sums; the theorem carries no asymptotic or distribution premise.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/TotalCycleVariance.lean#L165. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_FixedPointsPoisson
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_TotalCycleVariance
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_PMFToDistribution
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_RCyclesPoisson
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_ExpectedCycles
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

open Filter Asymptotics
open scoped BigOperators Topology

open AnalyticCombinatorics
open AnalyticCombinatorics.Ch9
open AnalyticCombinatorics.Ch9.LimitLaws
open AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS

theorem AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.totalCycleCount_variance_eq_harmonic_sub_harmonic2 (n : ℕ) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (totalCycleCount n σ : ℝ) ^ 2) -
      (FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (totalCycleCount n σ : ℝ))) ^ 2
      = cycleH1 n - cycleH2 n := by sorry
