-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch2_Mappings_MappingComponentsNS_Sharp_expected_components_isEquivalent
-- name    : AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS.Sharp.expected_components_isEquivalent
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:42:35.079995+00:00
-- url     : https://prove2.me/theorems/740ceb30-aabf-4522-adc9-c65ec0f554ac
-- title:
--   Mapping component counts have mean asymptotic to half log n
-- statement:
--   Let $\mathcal F_n$ be all functions from $\{0,\ldots,n-1\}$ to itself. A point is periodic if $f^m(x)=x$ for some integer $m>0$. Define $Q(n)=\sum_{k=0}^{n-1}\prod_{j=1}^k(1-j/n)$ in the real numbers. For $f\in\mathcal F_n$, let $K(f)$ be the number of cyclic restrictions of the permutation induced by $f$ on its periodic points: a restriction is a nonempty subset of periodic points with a permutation whose iterates have one orbit, agreeing with $f$ on that subset. Thus $K(f)$ is the source functional-graph component count. As natural $n\to\infty$,
--
--   $$\frac1{n^n}\sum_{f\in\mathcal F_n}K(f)\sim\frac12\log n.$$
--
--   The logarithm is the real natural logarithm; this is an asymptotic for the finite mean, not a distributional convergence assertion.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/Mappings/MappingComponentsSharp.lean#L488. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_MappingComponents
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Sharp logarithmic asymptotic for mapping components

The expected number of connected components in a uniform random mapping on
`n` labels is asymptotic to `(1 / 2) log n`.
-/

open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch2 AnalyticCombinatorics.Ch2.Mappings AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS

open AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

-- The finite-sum comparisons below combine several imported analytic bounds;
-- a larger heartbeat budget avoids brittleness in the final asymptotic squeeze.
set_option maxHeartbeats 800000

theorem AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS.Sharp.expected_components_isEquivalent :
    (fun n : ℕ => (∑ f : Fin n → Fin n, (componentCount f : ℝ)) / (n : ℝ)^n)
      ~[atTop] (fun n : ℕ => Real.log (n : ℝ) / 2) := by sorry
