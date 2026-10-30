-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_egf_bell
-- name    : AnalyticCombinatorics.Ch1.CombClass.egf_bell
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-25T09:34:35.347048+00:00
-- url     : https://prove2.me/theorems/50c4c2d6-e31b-4286-a579-c16c89764a07
-- title:
--   The exponential generating function of labelled set partitions
-- statement:
--   Let $b_n$ count partitions of the labels $\{0,\ldots,n-1\}$ into nonempty unordered blocks, with the unique positive-size decoration on each block. These are the objects of the source's nonempty-block set class. Their factorial-normalized generating function over $\mathbb Q$ satisfies
--
--   $$\sum_{n\geq0}b_n\frac{X^n}{n!}=\exp\bigl(\exp(X)-1\bigr).$$
--
--   Both exponential expressions are formal power series and the outer exponential is composed with the zero-constant series $\exp(X)-1$. The empty partition gives $b_0=1$. The assertion concerns this finite partition class; no identification with a separately named Bell-number sequence is assumed.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/EGF/Applications.lean#L28 Source code license: Apache-2.0; immutable license text: https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE.

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch2 §II.3 — Applications of the labelled symbolic method

Flajolet & Sedgewick, Part A, Chapter II, §II.3. Using the labelled set and
sequence transfers on the positive-integer ("urn"/nonempty-block) class `ℙ`
(one object of each size `n ≥ 1`, EGF `e^z - 1`):

* set partitions / **Bell numbers** `SET(ℙ)`, EGF `exp(e^z - 1)`;
* **surjections** `SEQ(ℙ)`, EGF `1/(2 - e^z)`.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries

theorem AnalyticCombinatorics.Ch1.CombClass.egf_bell :
    CombClass.posInt.set.egf = (PowerSeries.exp ℚ).subst (PowerSeries.exp ℚ - 1) := by sorry
