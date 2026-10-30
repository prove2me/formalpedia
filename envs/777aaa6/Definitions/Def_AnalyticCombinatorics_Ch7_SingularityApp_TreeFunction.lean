-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TreeFunction
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_TreeFunction
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T18:44:09.217531+00:00
-- url     : https://prove2.me/theorems/80919d38-1aad-4002-889f-e1587d832038
-- title:
--   Rooted Cayley coefficients, Stirling scales and numerical samples
-- statement:
--   The natural sequence is n^(n-1), and its real normalized coefficient is n^(n-1)/n!. The Stirling scale is sqrt(2n*pi)(n/exp(1))^n. Separate Float functions compute sample values and ratios using floating-point pi; these numerical functions are not proof certificates or error bounds.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/TreeFunction.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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
# Cayley tree-function coefficient asymptotic

The tree function

`T(z) = sum_{n >= 1} n^(n-1) z^n / n!`

has coefficients given exactly by Cayley's rooted labelled tree count.  This
file proves the coefficient asymptotic directly from Stirling's formula:

`n^(n-1) / n! ~ exp n / (sqrt (2*pi) * n^(3/2))`.

The exponent is `3/2`, not `5/2`: Stirling contributes
`1 / sqrt(2*pi*n)` and the quotient `n^(n-1) / n^n` contributes one more
factor `1/n`.
-/

open Filter Asymptotics
open scoped Topology

namespace AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS

/-- Cayley's count of rooted labelled trees on `n` labelled vertices. -/
def cayleyRootedTree (n : ℕ) : ℕ :=
  n ^ (n - 1)

/-- The coefficient sequence of the rooted labelled tree EGF. -/
noncomputable def treeFunctionCoeff (n : ℕ) : ℝ :=
  (cayleyRootedTree n : ℝ) / n.factorial

/-- The Stirling scale used by Mathlib's Stirling theorem. -/
noncomputable def treeStirlingScale (n : ℕ) : ℝ :=
  Real.sqrt (2 * (n : ℝ) * Real.pi) * (((n : ℝ) / Real.exp 1) ^ n)

def piFloat : Float :=
  3.141592653589793

def cayleyCoeffFloat (n : ℕ) : Float :=
  n.toFloat ^ (n - 1).toFloat / n.factorial.toFloat

def cayleyAsymptoticFloat (n : ℕ) : Float :=
  Float.exp n.toFloat /
    (Float.sqrt (2.0 * piFloat) * Float.pow n.toFloat 1.5)

def cayleyAsymptoticRatio (n : ℕ) : Float :=
  cayleyCoeffFloat n / cayleyAsymptoticFloat n

end AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS


