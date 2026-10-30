-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_Forests
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_Forests
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T18:13:25.039987+00:00
-- url     : https://prove2.me/theorems/754c8d1f-9885-4623-aefb-fb14e7217334
-- title:
--   Asymptotics of the defined rooted-forest sequence
-- statement:
--   For natural numbers $n$, define the closed-form sequence and its factorial normalization by
--
--   $$f_n=(n+1)^{n-1},\qquad c_n=\frac{f_n}{n!}.$$
--
--   The exponent uses natural subtraction, so $f_0=1$. The module also provides floating-point approximations to the normalized sequence and its asymptotic scale for numerical display. These definitions assert no forest-datatype cardinality or SET-of-tree equivalence.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/Forests.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

namespace AnalyticCombinatorics.Ch7.SingularityApp.ForestsNS

/-- Cayley's count of rooted labelled forests on `n` labelled vertices. -/
def rootedForest (n : ℕ) : ℕ :=
  (n + 1) ^ (n - 1)

/-- The coefficient sequence of the rooted labelled forest EGF `exp(T(z))`. -/
noncomputable def rootedForestCoeff (n : ℕ) : ℝ :=
  (rootedForest n : ℝ) / n.factorial

def forestPiFloat : Float :=
  3.141592653589793

def rootedForestCoeffFloat (n : ℕ) : Float :=
  (n.toFloat + 1.0) ^ (n - 1).toFloat / n.factorial.toFloat

def rootedForestAsymptoticFloat (n : ℕ) : Float :=
  Float.exp 1.0 * Float.exp n.toFloat /
    (Float.sqrt (2.0 * forestPiFloat) * Float.pow n.toFloat 1.5)

def rootedForestAsymptoticRatio (n : ℕ) : Float :=
  rootedForestCoeffFloat n / rootedForestAsymptoticFloat n

end AnalyticCombinatorics.Ch7.SingularityApp.ForestsNS


