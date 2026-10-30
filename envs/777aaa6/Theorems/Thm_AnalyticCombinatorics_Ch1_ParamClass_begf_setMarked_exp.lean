-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_ParamClass_begf_setMarked_exp
-- name    : AnalyticCombinatorics.Ch1.ParamClass.begf_setMarked_exp
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-25T10:33:41.605723+00:00
-- url     : https://prove2.me/theorems/54f83041-6846-465a-ac6c-9cae7967c60c
-- title:
--   Block-marked exponential formula for decorated labelled sets
-- statement:
--   Let $C$ be a family of finite object types indexed by natural sizes, with no size-zero objects. Write $A(z)=\sum_{n\geq0}|C_n|z^n/n!$. A decorated labelled set object is a partition of $n$ labels into nonempty unordered blocks, with one $C_{|B|}$-object on each block $B$. Mark each object by its number of blocks. If $a_{n,k}$ counts objects of size $n$ with $k$ blocks, then in $\mathbb Q[u][[z]]$,
--
--   $$\sum_{n\geq0}\left(\sum_{k\geq0}a_{n,k}u^k\right)\frac{z^n}{n!}=\exp\bigl(uA(z)\bigr).$$
--
--   The inner size-$n$ marking sum is a finite polynomial. The outer exponential is formal substitution into the exponential series over $\mathbb Q[u]$, not analytic evaluation. The empty labelled set contributes one object with zero blocks.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch3/BGF/LabelledSetMarked.lean#L567. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_SeqMarked
import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_LabelledSeqMarked
import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_LabelledSetMarked
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch3 -- Bivariate EGF transfer theorem for marked labelled sets

For a labelled class `C`, `setMarked C` is `SET(C)` with the number of blocks
marked by the parameter variable `u`. Its bivariate EGF is

  `F(z,u) = exp(u C(z))`,

represented here as substitution into `PowerSeries.exp ℚ[X]`.
-/

open scoped Polynomial

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries Finset

theorem AnalyticCombinatorics.Ch1.ParamClass.begf_setMarked_exp (C : CombClass) (hC : C.counts 0 = 0) :
    (ParamClass.setMarked C).begf =
      (PowerSeries.exp ℚ[X]).subst
        (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf) := by sorry
