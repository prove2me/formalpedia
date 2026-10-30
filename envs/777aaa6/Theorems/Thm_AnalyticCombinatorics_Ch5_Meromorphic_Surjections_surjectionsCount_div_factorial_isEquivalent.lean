-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch5_Meromorphic_Surjections_surjectionsCount_div_factorial_isEquivalent
-- name    : AnalyticCombinatorics.Ch5.Meromorphic.Surjections.surjectionsCount_div_factorial_isEquivalent
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T20:08:32.36419+00:00
-- url     : https://prove2.me/theorems/ebf08672-338d-426a-a563-4acac42a0124
-- title:
--   Factorial-normalized ordered nonempty-block counts
-- statement:
--   Let $S_n$ be the source labelled sequence of the class with one object in every positive size and none in size zero (`CombClass.posInt.lseq`), with its literal finite fibre model. Then, after rational normalization and embedding into $\mathbb C$, $$\frac{S_n}{n!}\sim\frac1{2(\log2)^{n+1}}.$$ No additional bijection with a separately defined surjection datatype is asserted.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch5/Meromorphic/Surjections.lean#L542. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_Surjections
import Mathlib
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

open AnalyticCombinatorics
open AnalyticCombinatorics.Ch5
open AnalyticCombinatorics.Ch5.Meromorphic
open AnalyticCombinatorics.Ch5.Meromorphic.Surjections

open AnalyticCombinatorics.Ch1

open AnalyticCombinatorics.Ch5.Meromorphic.Surjections.PowerSeries

theorem AnalyticCombinatorics.Ch5.Meromorphic.Surjections.surjectionsCount_div_factorial_isEquivalent :
    (fun n : ℕ =>
      algebraMap ℚ ℂ ((surjectionsCount n : ℚ) / (n.factorial : ℚ)))
      ~[atTop]
    (fun n : ℕ => (1 : ℂ) / (2 * (((Real.log 2 : ℝ) : ℂ) ^ (n + 1)))) := by sorry
