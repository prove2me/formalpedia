-- Prove2me | Theorems.Thm_FragmentedPermHAdmissible_fragPermThirdLocal_poly_bound
-- name    : FragmentedPermHAdmissible.fragPermThirdLocal_poly_bound
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:43:16.934262+00:00
-- url     : https://prove2.me/theorems/44063adb-8af5-440b-ad67-dea9764ee98f
-- title:
--   Supporting lemma: fragPermThirdLocal poly bound
-- statement:
--   Supporting lemma from AnalyticCombinatorics/Ch8/SaddlePoint/FragmentedPermThirdOrder.lean.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma fragPermThirdLocal_poly_bound {y : ℝ} (hy0 : 0 ≤ y) :
--       let K : ℝ := fragPermThirdScaledRemainderConst
--       let S1 : ℝ := 10 * y ^ 3 + 10 * y ^ 4 + 40 * y ^ 5 + 10 * y ^ 6 + K * y ^ 7
--       let S2 : ℝ := 10 * y ^ 4 + 40 * y ^ 5 + 10 * y ^ 6 + K * y ^ 7
--       let S3 : ℝ := 10 * y ^ 6 + K * y ^ 7
--       let S4 : ℝ := 40 * y ^ 5 + 10 * y ^ 6 + K * y ^ 7
--       let G : ℝ := ∑ k ∈ Finset.range 36, y ^ k
--       Real.exp 1 * S1 ^ 5 + K * y ^ 7 +
--         (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) +
--         (3 * (10 * y ^ 3) ^ 2 * S4 + 3 * (10 * y ^ 3) * S2 ^ 2 + S2 ^ 3) +
--         S2 * (S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
--           S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3)
--           ≤ fragPermThirdLocalL1Const * G
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/FragmentedPermThirdOrder.lean#L2853. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Poles
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermThirdOrder
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
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
/-!
# Third-order saddle data for fragmented permutations

This file adds the finite-radius third-order correction layer for
`exp (z / (1 - z))`.  The proof uses the narrower finite-radius window
`(1-r)^(29/20)`, because the second-order window is too wide for an
`o((1-r)^2)` third-order remainder.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open FragmentedPermHAdmissible

theorem FragmentedPermHAdmissible.fragPermThirdLocal_poly_bound {y : ℝ} (hy0 : 0 ≤ y) :
    let K : ℝ := fragPermThirdScaledRemainderConst
    let S1 : ℝ := 10 * y ^ 3 + 10 * y ^ 4 + 40 * y ^ 5 + 10 * y ^ 6 + K * y ^ 7
    let S2 : ℝ := 10 * y ^ 4 + 40 * y ^ 5 + 10 * y ^ 6 + K * y ^ 7
    let S3 : ℝ := 10 * y ^ 6 + K * y ^ 7
    let S4 : ℝ := 40 * y ^ 5 + 10 * y ^ 6 + K * y ^ 7
    let G : ℝ := ∑ k ∈ Finset.range 36, y ^ k
    Real.exp 1 * S1 ^ 5 + K * y ^ 7 +
      (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) +
      (3 * (10 * y ^ 3) ^ 2 * S4 + 3 * (10 * y ^ 3) * S2 ^ 2 + S2 ^ 3) +
      S2 * (S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
        S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3)
        ≤ fragPermThirdLocalL1Const * G := by sorry
