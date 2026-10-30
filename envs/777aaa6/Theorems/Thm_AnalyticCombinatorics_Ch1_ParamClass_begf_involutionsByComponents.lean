-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_ParamClass_begf_involutionsByComponents
-- name    : AnalyticCombinatorics.Ch1.ParamClass.begf_involutionsByComponents
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:25:50.783432+00:00
-- url     : https://prove2.me/theorems/54b60645-6d9a-49a4-bc91-8e50a0456af6
-- title:
--   Marked labelled sets with components of sizes one or two
-- statement:
--   For a graded class $C$, the source $\operatorname{SET}_{u}(C)$ is its labelled set construction, with parameter equal to the number of component blocks. Its bivariate exponential generating function is $\sum_{n\ge0}\sum_xu^{\#\mathrm{blocks}(x)}z^n/n!\in\mathbb Q[u][[z]]$. Take $C_1$ and $C_2$ to be singletons and all other fibres empty (the source class `parts12`). Then
--
--   $$E_{\operatorname{SET}_{u}(C)}(z,u)=\exp\bigl(u(z+z^2/2)\bigr).$$
--
--   The factorial factor $1/2$ is retained. This is the source marked-set construction, without an additional identification with a separately defined permutation involution type.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch3/BGF/LabelledBGFApplications.lean#L27. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Fibonacci
import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_SeqMarked
import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_LabelledSeqMarked
import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_LabelledSetMarked
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch3 -- Bivariate EGF applications for marked labelled sets

Cheap specializations of `ParamClass.begf_setMarked_exp` for the standard
labelled examples from Chapter 2.
-/

open scoped Polynomial

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

theorem AnalyticCombinatorics.Ch1.ParamClass.begf_involutionsByComponents :
    (ParamClass.setMarked CombClass.parts12).begf =
      (PowerSeries.exp ℚ[X]).subst
        (PowerSeries.C (Polynomial.X : ℚ[X]) *
          liftU (PowerSeries.X + (2⁻¹ : ℚ) • PowerSeries.X ^ 2)) := by sorry
