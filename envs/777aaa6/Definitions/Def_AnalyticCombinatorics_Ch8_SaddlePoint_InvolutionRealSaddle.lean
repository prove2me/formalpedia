-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionRealSaddle
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionRealSaddle
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-27T22:55:57.644894+00:00
-- url     : https://prove2.me/theorems/977c2806-9a44-4ca7-9553-004869189e9b
-- title:
--   Real quadratic-exponential saddle scale
-- statement:
--   For \(n\in\mathbb N\), write \(r_n=(\sqrt{1+4n}-1)/2\) and \(B(r)=r+2r^2\). The real-valued function `involRealSaddleScale` is defined by
--   \[
--   S(n)=\frac{\exp(r_n+r_n^2/2)}{r_n^n\sqrt{2\pi B(r_n)}}.
--   \]
--   The definition uses the existing `involSaddleRadius` and `involSaddleBReal` functions.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/InvolutionRealSaddle.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionHAdmissible
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
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
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Involutions: the classical Moser–Wyman real saddle asymptotic

`involution_count_over_factorial_isEquivalent_saddle` (InvolutionHAdmissible) gives the abstract
H-admissible saddle estimate for the number of involutions `I_n = parts12.set.counts n` (permutations
with all cycles of length 1 or 2; EGF `exp(z + z²/2)`).  This file realifies the abstract scale to the
recognizable Moser–Wyman formula

  `I_n / n! ~ exp(r_n + r_n²/2) / ( r_n^n · √(2π · (r_n + 2 r_n²)) )`,   `r_n + r_n² = n`,

with `r_n = (√(1+4n) − 1)/2`.  "Unfold and realify" of `saddleScale`, mirroring `BellRealSaddle`.
-/

noncomputable section

open Filter Asymptotics
open scoped Topology Real

namespace InvolutionHAdmissible

/-- The classical real Moser–Wyman involution saddle scale. -/
noncomputable def involRealSaddleScale (n : ℕ) : ℝ :=
  Real.exp (involSaddleRadius n + (involSaddleRadius n) ^ 2 / 2) /
    ((involSaddleRadius n) ^ n *
      Real.sqrt (2 * Real.pi * involSaddleBReal (involSaddleRadius n)))

end InvolutionHAdmissible


