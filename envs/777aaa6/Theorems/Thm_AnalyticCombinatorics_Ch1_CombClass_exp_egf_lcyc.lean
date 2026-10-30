-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_exp_egf_lcyc
-- name    : AnalyticCombinatorics.Ch1.CombClass.exp_egf_lcyc
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T15:59:00.961287+00:00
-- url     : https://prove2.me/theorems/821c6488-5e83-4a4e-aa35-54a24a3762ae
-- title:
--   Exponentiating the labelled-cycle EGF gives the labelled-sequence EGF
-- statement:
--   For a graded class $C$ with finite size fibres, write $E_C(z)=\sum_{n\ge0}|C_n|z^n/n!\in\mathbb Q[[z]]$. Assume $C_0$ is empty. The source labelled cycle class $L(C)$ has no size-zero object. At size $n+1$, its objects are ordered labelled powers $C^{\star(k+1)}$ for $0\le k\le n$ whose first component block contains the largest label $n$; this fixes a canonical rotation. The labelled product splits a label set into two complementary blocks; the labelled powers are its iterates with the neutral size-zero class as zeroth power. Let $S(C)$ be the source finite labelled-sequence class. Then
--
--   $$\exp\bigl(E_{L(C)}(z)\bigr)=E_{S(C)}(z).$$
--
--   The exponential is the formal series substituted into a zero-constant-term series. This is the exact exponentiated identity; no formal logarithm or analytic logarithm is introduced.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/EGF/LabelledCycExp.lean#L43. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledCyc
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Order.Partition.Finpartition
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
# Ch2 §II.2 — The labelled cycle closed form `CYC(C) = log(1/(1-C))`

`LabelledCyc.lean` characterizes the labelled cycle EGF by its ODE
`CYC(C)' = C'·SEQ(C)` together with a zero constant term
(`egf_lcyc_ode`, `egf_lcyc_unique`). The literal F&S closed form is

  `CYC(C)(z) = log(1 / (1 - C(z)))`.

Mathlib has no formal-power-series logarithm, so we deliver this in the
equivalent **exponentiated** shape, which needs only `PowerSeries.exp`
(already used for `egf_set`):

  `exp(CYC(C)) = 1/(1 - C(z)) = SEQ(C)`.

Both `exp(CYC(C))` and `SEQ(C)` solve the linear ODE `G' = CYC(C)'·G` with
constant term `1`, hence coincide by `ode_unique`.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries

theorem AnalyticCombinatorics.Ch1.CombClass.exp_egf_lcyc (C : CombClass) (hC : C.counts 0 = 0) :
    (exp ℚ).subst C.lcyc.egf = C.lseq.egf := by sorry
