-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch9_LimitLaws_RCyclesPoissonNS_Complete_rCycles_tendstoInDistribution_poisson
-- name    : AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Complete.rCycles_tendstoInDistribution_poisson
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T15:18:49.315333+00:00
-- url     : https://prove2.me/theorems/645197a0-12d0-4fc0-8753-27c3935222f9
-- title:
--   Poisson limit for a fixed positive permutation-cycle length
-- statement:
--   Fix a positive natural cycle length $r$. For each $n$, choose a permutation $\sigma_n$ uniformly from the $n!$ permutations of $\{0,\ldots,n-1\}$. Let $C_r(\sigma_n)$ be its number of cycles of length exactly $r$, explicitly counting fixed points when $r=1$. Then
--
--   $$C_r(\sigma_n)\ \xrightarrow{\ d\ }\ \operatorname{Poisson}(1/r).$$
--
--   The selected statement compares these random variables on their varying finite permutation spaces with the identity variable on $\mathbb N$ under the Poisson measure of nonnegative-real rate $(r:\mathbb R_{\ge0})^{-1}$. Only $r>0$ is a public premise. The genuine PMF/counting and factorial-moment inputs are supplied by source theorems. The length $r$ remains fixed as $n\to\infty$; no growing-length limit, rate, finite-$n$ Poisson identity or independence of different cycle lengths is claimed. The unique empty permutation at $n=0$ has count zero.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/RCyclesPoissonComplete.lean#L335. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Compatibility_TendstoInDistribution
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_RCyclesPoisson
import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Completion of the fixed-length cycle Poisson limit

This file proves the finite Bonferroni/factorial-moment inversion needed to
identify the genuine `r`-cycle pmf with the closed inclusion-exclusion formula.
-/

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

open AnalyticCombinatorics
open AnalyticCombinatorics.Ch9
open AnalyticCombinatorics.Ch9.LimitLaws
open AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS

theorem AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Complete.rCycles_tendstoInDistribution_poisson {r : ℕ} (hr : 0 < r) :
    AnalyticCombinatorics.Compatibility.TendstoInDistribution
      (fun n (ω : Equiv.Perm (Fin n)) => rCycleCount n r ω)
      atTop
      (fun x : ℕ => x)
      uniformPermMeasure
      (ProbabilityTheory.poissonMeasure (poissonRate r)) := by sorry
