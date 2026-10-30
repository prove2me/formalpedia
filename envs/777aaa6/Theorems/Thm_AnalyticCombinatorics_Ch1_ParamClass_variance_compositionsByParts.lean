-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_ParamClass_variance_compositionsByParts
-- name    : AnalyticCombinatorics.Ch1.ParamClass.variance_compositionsByParts
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-25T10:33:33.431873+00:00
-- url     : https://prove2.me/theorems/713679cf-143c-449f-9903-749153f568b3
-- title:
--   Variance of the number of parts in a positive integer composition
-- statement:
--   For a natural number $n\geq1$, choose uniformly among all ordered compositions of $n$ into positive integer parts. If $K$ is the number of parts, then
--
--   $$\operatorname{Var}(K)=\frac{n-1}{4}.$$
--
--   The source represents variance by rational finite-sum moments of the length parameter on the actual composition objects. Its count is positive on the stated domain. The case $n=0$ is excluded; the empty composition would have variance zero rather than the displayed negative rational expression.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch3/BGF/CompositionMoments.lean#L160. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_Variance
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch3 -- Mean and variance for parts in compositions

For a fixed `n ≥ 1`, Mathlib's boundary-set equivalence identifies
compositions of `n` with subsets of `Fin (n - 1)`.  The number of parts is one
plus the number of chosen interior boundaries.
-/

open scoped Polynomial

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries Finset

theorem AnalyticCombinatorics.Ch1.ParamClass.variance_compositionsByParts {n : ℕ} (hn : 1 ≤ n) :
    ParamClass.compositionsByParts.variance n = ((n : ℚ) - 1) / 4 := by sorry
