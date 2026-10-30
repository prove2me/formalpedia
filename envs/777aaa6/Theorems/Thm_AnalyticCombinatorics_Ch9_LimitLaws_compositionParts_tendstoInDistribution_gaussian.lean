-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch9_LimitLaws_compositionParts_tendstoInDistribution_gaussian
-- name    : AnalyticCombinatorics.Ch9.LimitLaws.compositionParts_tendstoInDistribution_gaussian
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T15:58:26.532627+00:00
-- url     : https://prove2.me/theorems/d3e5c613-4daa-48ac-a413-81ccbca70447
-- title:
--   A Gaussian limit for the composition-gap part-count model
-- statement:
--   At size $n$, the source probability space is the real sign-gap product model with $n-1$ coordinates and law `compositionGapP n`; natural subtraction is used. On the full real-coordinate carrier define $K_n(\omega)=1+(\sum_i\omega_i+(n-1))/2$, where the natural number $n-1$ is cast to the reals. On the sign-supported product law this equals one plus the number of positive gaps. Then $$\frac{K_n-(n+1)/2}{\sqrt{(n-1)/4}}\ \Longrightarrow\ N(0,1).$$ Finite mass identities relate this gap model to composition counts for positive $n$ and positive part counts; this headline is stated on the gap model, without an extra random-variable transport to uniform composition objects. The source carriers and measures vary with $n$, and the limit is the identity random variable on $\mathbb R$ with the standard Gaussian measure.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/CompositionParts.lean#L259. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_BinaryWordCLT
import Definitions.Def_AnalyticCombinatorics_Compatibility_TendstoInDistribution
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_CompositionParts
import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Number of parts in a random composition

For `n ≥ 1`, a composition of `n` with `k` parts is equivalently a choice of
`k - 1` of the `n - 1` interior gaps.  Thus the part count has the same law as
`1 + Binomial(n - 1, 1 / 2)`.

The central limit theorem is proved by reusing the local quasi-powers
instantiation for binary words from `BinaryWordCLT.lean`, shifted from `n` to
`n - 1` and then translated by the deterministic `+1`.
-/

open Complex Filter MeasureTheory ProbabilityTheory

open scoped Topology

open AnalyticCombinatorics
open AnalyticCombinatorics.Ch9
open AnalyticCombinatorics.Ch9.LimitLaws

theorem AnalyticCombinatorics.Ch9.LimitLaws.compositionParts_tendstoInDistribution_gaussian :
    AnalyticCombinatorics.Compatibility.TendstoInDistribution
      (fun n ω =>
        (compositionParts n ω - ((n : ℝ) + 1) / 2) /
          Real.sqrt (((n - 1 : ℕ) : ℝ) / 4)) atTop
      (fun x : ℝ => x) compositionGapP (gaussianReal 0 1) := by sorry
