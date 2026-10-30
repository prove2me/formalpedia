-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_ParamClass_begf_setPartitionsByBlocks
-- name    : AnalyticCombinatorics.Ch1.ParamClass.begf_setPartitionsByBlocks
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:25:33.510792+00:00
-- url     : https://prove2.me/theorems/c0b68445-474e-4dc6-b64a-9418a5b4a5fd
-- title:
--   Marked labelled-set specialization with one component at each positive size
-- statement:
--   For a graded class $C$, the source $\operatorname{SET}_{u}(C)$ is its labelled set construction, with parameter equal to the number of component blocks. Its bivariate exponential generating function is $\sum_{n\ge0}\sum_xu^{\#\mathrm{blocks}(x)}z^n/n!\in\mathbb Q[u][[z]]$. Take $C_m$ to be a singleton for each $m\ge1$ and empty at zero (the source class `posInt`). Then
--
--   $$E_{\operatorname{SET}_{u}(C)}(z,u)=\exp\bigl(u(\exp(z)-1)\bigr).$$
--
--   The exponentials and substitution are formal. The theorem concerns this source labelled-set model; no extra equivalence to the separately defined `Finpartition` Bell model is asserted.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch3/BGF/LabelledBGFApplications.lean#L17. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

theorem AnalyticCombinatorics.Ch1.ParamClass.begf_setPartitionsByBlocks :
    (ParamClass.setMarked CombClass.posInt).begf =
      (PowerSeries.exp ℚ[X]).subst
        (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU (PowerSeries.exp ℚ - 1)) := by sorry
