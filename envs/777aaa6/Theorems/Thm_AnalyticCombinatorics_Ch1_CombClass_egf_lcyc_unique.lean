-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_egf_lcyc_unique
-- name    : AnalyticCombinatorics.Ch1.CombClass.egf_lcyc_unique
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T15:59:06.666922+00:00
-- url     : https://prove2.me/theorems/c89e983d-f8d1-4741-bcf8-73eb177fd6be
-- title:
--   Differential characterization of the labelled-cycle EGF
-- statement:
--   For a graded class $C$ with finite size fibres, write $E_C(z)=\sum_{n\ge0}|C_n|z^n/n!\in\mathbb Q[[z]]$. Assume $C_0$ is empty. The source labelled cycle class $L(C)$ has no size-zero object. At size $n+1$, its objects are ordered labelled powers $C^{\star(k+1)}$ for $0\le k\le n$ whose first component block contains the largest label $n$; this fixes a canonical rotation. The labelled product splits a label set into two complementary blocks; the labelled powers are its iterates with the neutral size-zero class as zeroth power. Let $S(C)$ be the source finite labelled-sequence class. If $F\in\mathbb Q[[z]]$ satisfies
--
--   $$F(0)=0,\qquad F'(z)=E_C'(z)\,E_{S(C)}(z),$$
--
--   then $F(z)=E_{L(C)}(z)$. Both conditions on $F$ and the hypothesis $C_0=\varnothing$ are retained.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/EGF/LabelledCyc.lean#L217. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledCyc
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch2 §II.2 — The labelled cycle construction

This file gives a concrete canonical-rotation model for labelled cycles.  A
nonempty labelled power represents a cycle by rotating it so that the first
block contains the largest label.  The transfer theorem is stated as the
defining differential equation

  `CYC(C)' = C' * SEQ(C)`, with zero constant term.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries Finset

theorem AnalyticCombinatorics.Ch1.CombClass.egf_lcyc_unique (C : CombClass) (hC : C.counts 0 = 0) {F : ℚ⟦X⟧}
    (hF' : d⁄dX ℚ F = d⁄dX ℚ C.egf * C.lseq.egf)
    (hF0 : constantCoeff F = 0) :
    F = C.lcyc.egf := by sorry
