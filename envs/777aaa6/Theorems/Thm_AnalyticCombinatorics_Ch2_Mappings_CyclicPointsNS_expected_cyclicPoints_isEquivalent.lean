-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch2_Mappings_CyclicPointsNS_expected_cyclicPoints_isEquivalent
-- name    : AnalyticCombinatorics.Ch2.Mappings.CyclicPointsNS.expected_cyclicPoints_isEquivalent
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:43:04.993004+00:00
-- url     : https://prove2.me/theorems/dfdf29f8-70a0-49fd-bf08-4b794e63e393
-- title:
--   Asymptotic mean number of cyclic points
-- statement:
--   Let $\mathcal F_n$ be all functions from $\{0,\ldots,n-1\}$ to itself. A point is periodic if $f^m(x)=x$ for some integer $m>0$. Define $Q(n)=\sum_{k=0}^{n-1}\prod_{j=1}^k(1-j/n)$ in the real numbers. With $Z(f)$ the number of periodic points, as natural $n\to\infty$,
--
--   $$\frac1{n^n}\sum_{f\in\mathcal F_n}Z(f)\sim\sqrt{\frac{\pi n}{2}}.$$
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/Mappings/CyclicPoints.lean#L669. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_ConnectedMappings
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Cyclic points in random mappings

This file counts mappings for which a fixed point is cyclic and derives the
expected number of cyclic points from Ramanujan's finite `Q`-function.
-/

open Filter Asymptotics
open scoped BigOperators Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch2 AnalyticCombinatorics.Ch2.Mappings

open AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS

theorem AnalyticCombinatorics.Ch2.Mappings.CyclicPointsNS.expected_cyclicPoints_isEquivalent :
    (fun n : ℕ => (∑ f : Fin n → Fin n, ((periodicPointsFinset f).card : ℝ)) / (n:ℝ)^n)
      ~[atTop] (fun n : ℕ => Real.sqrt (Real.pi * n / 2)) := by sorry
