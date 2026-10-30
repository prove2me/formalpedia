-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch5_Meromorphic_CompositionsGeneral_Close_compS_isEquivalent
-- name    : AnalyticCombinatorics.Ch5.Meromorphic.CompositionsGeneral.Close.compS_isEquivalent
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-25T15:35:32.423348+00:00
-- url     : https://prove2.me/theorems/ee957944-d39b-457e-96dd-de9095d4b3cf
-- title:
--   Asymptotic counts of compositions with a fixed finite positive part set
-- statement:
--   Fix a finite set $S\subset\mathbb N$ with $0\notin S$, $|S|\ge2$, and $\gcd\{s:s\in S\}=1$. Let $\operatorname{comp}_S(n)$ be the number of finite ordered lists of elements of $S$ whose sum is $n$; the empty list is included when $n=0$. Put
--
--   $$P_S(z)=\sum_{s\in S}z^s,\qquad
--   P'_S(z)=\sum_{s\in S}s\,z^{s-1}.$$
--
--   Let $\rho$ be the unique positive real root of $P_S(\rho)=1$. Under the stated assumptions $0<\rho<1$ and $P'_S(\rho)>0$. Then, for this fixed $S$, as natural $n\to\infty$,
--
--   $$\operatorname{comp}_S(n)\sim\frac{\rho^{-n}}{\rho P'_S(\rho)}.$$
--
--   In the Lean statement the natural count and the real root are embedded in $\mathbb C$, and the comparison constant is $1/(\rho P'_S(\rho))$. The theorem assumes only the displayed finite-set conditions; an analytic remainder or a coefficient asymptotic is not an additional hypothesis. The assertion has no uniformity claim for sets $S$ varying with $n$.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch5/Meromorphic/CompositionsGeneralClose.lean#L398. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_CompositionsGeneral
import Mathlib
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Closing the general finite-part composition family

This file supplies the formal OGF bridge, the derivative nonvanishing input, and the
dominant-pole decomposition needed by `CompositionsGeneral`.
-/

open Complex Filter Asymptotics
open scoped BigOperators ComplexOrder ENNReal NNReal PowerSeries Topology

open AnalyticCombinatorics
open AnalyticCombinatorics.Ch5
open AnalyticCombinatorics.Ch5.Meromorphic
open AnalyticCombinatorics.Ch5.Meromorphic.CompositionsGeneral

theorem AnalyticCombinatorics.Ch5.Meromorphic.CompositionsGeneral.Close.compS_isEquivalent
    (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S)
    (hgcd : S.gcd id = 1) :
    (fun n : ℕ => (compS S h0 n : ℂ)) ~[atTop]
      (fun n : ℕ =>
        compAsymptoticConstant S hcard h0 * (rhoSℂ S hcard h0)⁻¹ ^ n) := by sorry
