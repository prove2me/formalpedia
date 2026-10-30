-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_egf_set
-- name    : AnalyticCombinatorics.Ch1.CombClass.egf_set
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-25T09:34:48.328107+00:00
-- url     : https://prove2.me/theorems/4cb7217e-fb5d-472d-a459-c966a018e0df
-- title:
--   The exponential formula for decorated labelled set partitions
-- statement:
--   Let $C_m$ be a finite type of objects for each natural-number size $m$, and assume that $C_0$ is empty. Let $c_m=|C_m|$ and $A(X)=\sum_{m\geq0}c_mX^m/m!$ over $\mathbb Q$. A size-$n$ set object is a partition of the labels $\{0,\ldots,n-1\}$ into nonempty unordered blocks, together with one $C_{|B|}$-object for every block $B$. If $s_n$ counts these decorated partitions and $S(X)=\sum_{n\geq0}s_nX^n/n!$, then
--
--   $$S(X)=\exp(A(X)).$$
--
--   This is formal substitution into $\exp(X)=\sum_{k\geq0}X^k/k!$. The zero-size condition makes $A(0)=0$, and the empty partition gives $s_0=1$. No analytic convergence is required.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/EGF/LabelledSetExp.lean#L26 Source code license: Apache-2.0; immutable license text: https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE.

import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch2 §II.2 — The labelled set exponential formula

This file closes the labelled SET construction:
`SET(C)(z) = exp(C(z))` when `C` has no size-zero objects.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries

theorem AnalyticCombinatorics.Ch1.CombClass.egf_set (C : CombClass) (hC : C.counts 0 = 0) :
    C.set.egf = (PowerSeries.exp ℚ).subst C.egf := by sorry
