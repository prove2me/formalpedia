-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch7_SingularityApp_LabeledTreeNS_card_rootedLabeledTree_one
-- name    : AnalyticCombinatorics.Ch7.SingularityApp.LabeledTreeNS.card_rootedLabeledTree_one
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:12:37.593828+00:00
-- url     : https://prove2.me/theorems/ceeb3a78-93c3-4896-bb62-87b8f0d71ab8
-- title:
--   A rooted graph-tree base case on one label
-- statement:
--   For the source finite type of rooted simple-graph trees on the one-element set, $$|\operatorname{RootedLabeledTree}(1)|=1.$$ This is a base case. The fixed source module supplies graph-tree cases at sizes zero and one, not a general graph Cayley theorem or a Prüfer bridge.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/Cayley.lean#L48. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_LabeledTreeBasic
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

namespace AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS end AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Cayley's formula: cardinalities of labelled trees

This file collects the cardinality results for `LabeledTree` and
`RootedLabeledTree` and connects them to the banked `cayleyRootedTree`.

The base cases `n = 0` and `n = 1` are proved here directly.  The general
`n ≥ 2` case (via the Prüfer bijection) lives in `Prufer.lean`; this file
assembles the final connection.
-/

open AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS

open AnalyticCombinatorics AnalyticCombinatorics.Ch7 AnalyticCombinatorics.Ch7.SingularityApp AnalyticCombinatorics.Ch7.SingularityApp.LabeledTreeNS

theorem AnalyticCombinatorics.Ch7.SingularityApp.LabeledTreeNS.card_rootedLabeledTree_one : Fintype.card (RootedLabeledTree 1) = 1 := by sorry
