-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch2_Mappings_CyclicPointsNS_expected_cyclicPoints_eq_q
-- name    : AnalyticCombinatorics.Ch2.Mappings.CyclicPointsNS.expected_cyclicPoints_eq_q
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:42:14.377403+00:00
-- url     : https://prove2.me/theorems/ac510ec2-f2b8-4fe3-ab33-ab98242a55dc
-- title:
--   The exact mean number of cyclic points is Ramanujan Q
-- statement:
--   Let $\mathcal F_n$ be all functions from $\{0,\ldots,n-1\}$ to itself. A point is periodic if $f^m(x)=x$ for some integer $m>0$. Define $Q(n)=\sum_{k=0}^{n-1}\prod_{j=1}^k(1-j/n)$ in the real numbers. Write $Z(f)=|\{x:f^m(x)=x\text{ for some }m>0\}|$. For $n>0$,
--
--   $$\frac1{n^n}\sum_{f\in\mathcal F_n}Z(f)=Q(n).$$
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/Mappings/CyclicPoints.lean#L617. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_RamanujanQ
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

theorem AnalyticCombinatorics.Ch2.Mappings.CyclicPointsNS.expected_cyclicPoints_eq_q {n : ℕ} (hn : 0 < n) :
    (∑ f : Fin n → Fin n, ((periodicPointsFinset f).card : ℝ)) / (n : ℝ)^n =
      AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.ramanujanQ n := by sorry
