-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch2_Mappings_MappingComponentsNS_expected_components_eq
-- name    : AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS.expected_components_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:43:06.323987+00:00
-- url     : https://prove2.me/theorems/4d3dae21-f1ce-4d56-bec9-ee033ebd9638
-- title:
--   An exact finite sum for the mean number of mapping components
-- statement:
--   Let $\mathcal F_n$ be all functions from $\{0,\ldots,n-1\}$ to itself. A point is periodic if $f^m(x)=x$ for some integer $m>0$. Define $Q(n)=\sum_{k=0}^{n-1}\prod_{j=1}^k(1-j/n)$ in the real numbers. For $f\in\mathcal F_n$, let $K(f)$ be the number of cyclic restrictions of the permutation induced by $f$ on its periodic points: a restriction is a nonempty subset of periodic points with a permutation whose iterates have one orbit, agreeing with $f$ on that subset. Thus $K(f)$ is the source functional-graph component count. For $n>0$,
--
--   $$\frac1{n^n}\sum_{f\in\mathcal F_n}K(f)=\sum_{k=1}^n\frac{n^{\underline k}}{k\,n^k}.$$
--
--   Both the averaging denominator and the factor $k$ in each summand are part of the formula.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/Mappings/MappingComponents.lean#L280. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_MappingComponents
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Components of random mappings

The component count is defined as the number of nonempty single-cycle
restrictions of the permutation induced by a mapping on its periodic core.  A
candidate cycle `C` of a map is counted exactly when the ambient map restricts
to a cyclic permutation on `C`; this is equivalent to being one cycle of the
periodic-core permutation.
-/

open Filter Asymptotics
open scoped BigOperators Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch2 AnalyticCombinatorics.Ch2.Mappings AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS

open AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS
open AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

theorem AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS.expected_components_eq {n : ℕ} (hn : 0 < n) :
    (∑ f : Fin n → Fin n, (componentCount f : ℝ)) / (n : ℝ)^n
      = ∑ k ∈ Finset.Icc 1 n,
          (n.descFactorial k : ℝ) / ((k : ℝ) * (n : ℝ)^k) := by sorry
