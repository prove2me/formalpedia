-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch7_SingularityApp_ForestsNS_rootedForest_over_factorial_isEquivalent_exp_add
-- name    : AnalyticCombinatorics.Ch7.SingularityApp.ForestsNS.rootedForest_over_factorial_isEquivalent_exp_add
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T18:15:11.45241+00:00
-- url     : https://prove2.me/theorems/4ae4c013-83ee-4db5-b091-b77d90559a8f
-- title:
--   Asymptotics of the defined rooted-forest sequence
-- statement:
--   Define the natural-number sequence $f_n=(n+1)^{n-1}$ using natural subtraction in the exponent (so $f_0=1$). Then $$\frac{f_n}{n!}\sim\frac{e^{n+1}}{\sqrt{2\pi}\,n^{3/2}}.$$ Here `rootedForest` is this closed-form sequence; this theorem supplies no forest-datatype cardinality or SET-of-tree equivalence.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/Forests.lean#L158. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_Forests
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Rooted labelled forests

A rooted labelled forest on `[n]` is a finite SET of rooted labelled Cayley
trees.  Its EGF is `F(z) = exp(T(z))`, where `T = z exp T` is the tree
function.  The classical Cayley-Prüfer count is

`rootedForest n = (n + 1)^(n - 1)`.

Equivalently, the forest EGF coefficient is the next tree-function
coefficient:

`rootedForest n / n! = treeFunctionCoeff (n + 1)`.

The asymptotic therefore follows from the tree-function Stirling asymptotic,
with the shift contributing the extra factor `exp 1`.
-/

open Filter Asymptotics
open scoped Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch7 AnalyticCombinatorics.Ch7.SingularityApp AnalyticCombinatorics.Ch7.SingularityApp.ForestsNS

theorem AnalyticCombinatorics.Ch7.SingularityApp.ForestsNS.rootedForest_over_factorial_isEquivalent_exp_add :
    (fun n : ℕ => (rootedForest n : ℝ) / n.factorial) ~[atTop]
      (fun n : ℕ =>
        Real.exp ((n : ℝ) + 1) /
          (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)))) := by sorry
