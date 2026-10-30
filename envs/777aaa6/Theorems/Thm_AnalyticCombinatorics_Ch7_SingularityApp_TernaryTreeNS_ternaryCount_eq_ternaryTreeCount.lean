-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTreeNS_ternaryCount_eq_ternaryTreeCount
-- name    : AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS.ternaryCount_eq_ternaryTreeCount
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:12:44.389748+00:00
-- url     : https://prove2.me/theorems/90da0085-b48b-48aa-beb1-1eceec47421b
-- title:
--   Recursive ordered ternary trees and their closed count sequence
-- statement:
--   The source ternary trees have a leaf constructor and an ordered node with three recursive children. Write $T_n$ for their count at size $n$ and $t_n$ for the separately defined ternary Fuss–Catalan sequence. For every $n\in\mathbb N$, including zero, $$T_n=t_n.$$
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/TernaryLagrange.lean#L243. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTreeBasic
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTrees
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTreeRecurrence
import Mathlib
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

namespace AnalyticCombinatorics.Ch1.Lagrange end AnalyticCombinatorics.Ch1.Lagrange

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ternary trees via Lagrange inversion

We close the ternary-tree Fuss–Catalan closed form
`ternaryCount n = C(3n, n) / (2n + 1) = ternaryTreeCount n`
through the banked Ch1 Lagrange inversion machinery, mirroring the Catalan
worked example `coeff_implicitSeries_one_add_X_sq` with a cube.

The generating function `B = ∑ ternaryCount n · zⁿ` satisfies `B = 1 + z·B³`, so
`T := B - 1` satisfies `T = z·(1 + T)³ = z·((1+X)³).subst T`. By
`implicitSeries_unique`, `T = implicitSeries ((1+X)³)`, whose `n`-th coefficient
(for `0 < n`) is `(1/n)·C(3n, n-1) = C(3n, n)/(2n+1)` by Lagrange inversion.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch7 AnalyticCombinatorics.Ch7.SingularityApp AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS

open PowerSeries
open AnalyticCombinatorics.Ch1.Lagrange
open scoped BigOperators

/-! ## Part B.1 — Lagrange coefficient of `implicitSeries ((1+X)³)` -/


/-! ## Part B.2 — connect `ternaryCount` to `implicitSeries ((1+X)³)` -/

/-! ## Part B.3 — final Fuss–Catalan closed form + connection to `ternaryTreeCount` -/

theorem AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS.ternaryCount_eq_ternaryTreeCount (n : ℕ) :
    ternaryCount n = _root_.ternaryTreeCount n := by sorry
