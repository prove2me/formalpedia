-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_ogf_cyc
-- name    : AnalyticCombinatorics.Ch1.CombClass.ogf_cyc
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:25:37.174619+00:00
-- url     : https://prove2.me/theorems/11bb22ab-8597-4789-b470-2dbda5ba1112
-- title:
--   Totient formula for the ordinary cycle construction
-- statement:
--   For a graded class $C$ of finite sets, write $c_n=|C_n|$ and $A_C(z)=\sum_{n\ge0}c_nz^n\in\mathbb Q[[z]]$. Assume $c_0=0$. A size-$n$ cycle is a rotation orbit of a word indexed by $\mathbb Z/k\mathbb Z$, for some $1\le k\le n$, whose letters are $C$-objects of total size $n$. Let $\operatorname{mlog}(f)=\sum_{j\ge1}f^j/j$ and let $\varphi$ be Euler’s totient function. Then
--
--   $$A_{\operatorname{CYC}(C)}(z)=\sum_{d\ge1}\frac{\varphi(d)}d\operatorname{mlog}\bigl(A_C(z^d)\bigr).$$
--
--   Substitution by $z^d$ is formal power-series substitution. The zero-size hypothesis and coefficientwise topology are part of this result.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/CycleOGF.lean#L684. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_CycleOGF
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Topology.Instances.Rat
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch1 §I.2 — The cycle construction OGF layer

This file connects the Burnside count for cycle necklaces to the ordinary
generating function identity

  `CYC(C)(z) = ∑_{d ≥ 1} φ(d)/d * mlog(C(z^d))`.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open scoped BigOperators PowerSeries.WithPiTopology
open PowerSeries
open PowerSeries.WithPiTopology

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instTopRatCycleOGF

local instance _root_.AnalyticCombinatorics.Ch1.instDiscRatCycleOGF : DiscreteTopology ℚ := ⟨rfl⟩

theorem AnalyticCombinatorics.Ch1.CombClass.ogf_cyc
    (C : CombClass) (hC0 : C.counts 0 = 0) :
    C.cyc.ogf = cycRHS C := by sorry
