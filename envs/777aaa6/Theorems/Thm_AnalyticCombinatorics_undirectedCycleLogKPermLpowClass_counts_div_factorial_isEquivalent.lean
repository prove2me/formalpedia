-- Prove2me | Theorems.Thm_AnalyticCombinatorics_undirectedCycleLogKPermLpowClass_counts_div_factorial_isEquivalent
-- name    : AnalyticCombinatorics.undirectedCycleLogKPermLpowClass_counts_div_factorial_isEquivalent
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:57:52.327153+00:00
-- url     : https://prove2.me/theorems/5d9a7865-ab90-4104-bd88-8fd2d15444ab
-- title:
--   An undirected cycle with labelled powers of cycle-marked permutations
-- statement:
--   The source labelled product allocates disjoint blocks of a label set to its factors. Let $\mathcal P_n$ be the actual finite permutation type $\operatorname{Equiv.Perm}(\operatorname{Fin}n)$ and $\mathcal M=\operatorname{LCYC}(\mathcal Z)\star\mathcal P$, so one cycle is distinguished. Let $\mathcal U$ be the source cycle class formed from single-cycle permutations modulo reversal, restricted to lengths at least three. For every fixed natural $k\ge2$, the class $\mathcal U\star\mathcal M^{\star k}$ satisfies $$\frac{|(\mathcal U\star\mathcal M^{\star k})_n|}{n!}\sim\frac{n^{k-1}(\log n)^{k+1}}{2(k-1)!}.$$ The powers use disjoint label blocks; they are not independent permutations on one shared carrier.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/UndirectedCycleLogKPermLpow.lean#L191. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledProduct
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledPower
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSetOde
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TwoRegularClass
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSeq
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledCyc
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_CycleMarkedPermPairs
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_CycleMarkedPermLpow
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_UndirectedCycleLogKPermLpow
import Mathlib
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.Card
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Complex.Liouville

namespace AnalyticCombinatorics.Ch5.Meromorphic.Alignments end AnalyticCombinatorics.Ch5.Meromorphic.Alignments

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Undirected cycles times marked-cycle permutation `k`-tuples

`undirectedCycleLogKPermLpowClass k := undirectedCycleClass ⋆ cycleMarkedPermLpowClass k`
has EGF

  `(1/2 * log(1/(1-z)) - z/2 - z^2/4) * (1-z)^{-k} * log(1/(1-z))^k`

so its dominant term is

  `1/2 * (1-z)^{-k} * (-log(1-z))^{k+1}`.

The residual is a natural log-remainder, giving

  `a_n / n! ~ 1/2 * n^{k-1}/(k-1)! * (log n)^{k+1}`.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

open AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

theorem AnalyticCombinatorics.undirectedCycleLogKPermLpowClass_counts_div_factorial_isEquivalent {k : ℕ}
    (hk : 2 ≤ k) :
    (fun n : ℕ => ((undirectedCycleLogKPermLpowClass k).counts n : ℝ) / (n.factorial : ℝ))
      ~[atTop]
    (fun n : ℕ =>
      (1 / 2 : ℝ) * (n : ℝ) ^ (k - 1) / ((k - 1).factorial : ℝ)
        * (Real.log n) ^ (k + 1)) := by sorry
