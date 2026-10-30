-- Prove2me | Theorems.Thm_AnalyticCombinatorics_undirectedCycleLogSqPermPairClass_counts_div_factorial_isEquivalent
-- name    : AnalyticCombinatorics.undirectedCycleLogSqPermPairClass_counts_div_factorial_isEquivalent
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:57:18.550603+00:00
-- url     : https://prove2.me/theorems/77ac04a6-df78-4d7b-a264-a39d588cca54
-- title:
--   An undirected cycle with the source marked permutation pair
-- statement:
--   The source labelled product allocates disjoint blocks of a label set to its factors. Let $\mathcal P_n$ be the actual finite permutation type $\operatorname{Equiv.Perm}(\operatorname{Fin}n)$ and $\mathcal M=\operatorname{LCYC}(\mathcal Z)\star\mathcal P$, so one cycle is distinguished. Let $\mathcal U$ be the source cycle class formed from single-cycle permutations modulo reversal, restricted to lengths at least three. The class $\mathcal A=\mathcal U\star(\mathcal M\star\mathcal P)$, exactly `undirectedCycleLogSqPermPairClass`, has $$\frac{|\mathcal A_n|}{n!}\sim\tfrac12 n(\log n)^2.$$ Its exact product definition is retained in the model blocks; no same-label tuple interpretation is added.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/UndirectedCycleLogSqPermPair.lean#L154. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_UndirectedCycleLogSqPermPair
import Mathlib
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
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
# A class that GENUINELY needs the natural-remainder log² transfer (~½·n·(log n)²)

`undirectedCycleLogSqPermPairClass := undirectedCycleClass ⋆ cycleMarkedPermPairClass` — an
undirected cycle (length ≥ 3) together with an ordered pair of permutations one of whose cycles is
distinguished — has EGF

  `(½·log(1/(1-z)) - z/2 - z²/4) · log(1/(1-z)) · (1-z)^{-2}`
    `= ½·(1-z)^{-2}·(-log(1-z))²  -  (z/2 + z²/4)·(1-z)^{-2}·(-log(1-z))`.

The residual `R(z) = -(z/2+z²/4)·(1-z)^{-2}·(-log(1-z))` has `‖R‖·‖1-z‖² ≍ |log(1-z)| → ∞`
(so it is NOT `o(|1-z|^{-2})` — the *strong* log² transfer fails), yet
`‖R‖·‖1-z‖²/log²(1/|1-z|) → 0` (so the *natural* log² transfer applies).  Hence

  `aₙ / n! ~ ½·n·(log n)²`.

This is the first class requiring the natural-remainder log² transfer (analog of
`undirectedCycleMarkedPermPairs` for log¹).  (Construction from ChatGPT-Pro ac/ac2.)
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

open AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

theorem AnalyticCombinatorics.undirectedCycleLogSqPermPairClass_counts_div_factorial_isEquivalent :
    (fun n : ℕ => (undirectedCycleLogSqPermPairClass.counts n : ℝ) / (n.factorial : ℝ)) ~[atTop]
      (fun n : ℕ => (1 / 2 : ℝ) * (n : ℝ) * (Real.log n) ^ 2) := by sorry
