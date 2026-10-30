-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3RealSaddle
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3RealSaddle
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T02:45:21.475991+00:00
-- url     : https://prove2.me/theorems/fb881616-66ac-4d4c-be6f-c1ce83daca2c
-- title:
--   Real cubic-exponential saddle scale
-- statement:
--   For \(n\in\mathbb N\), with \(r_n=\texttt{blocks3SaddleRadius}(n)\) and \(B(r)=r+2r^2+3r^3/2\), the real-valued function `blocks3RealSaddleScale` is defined by
--   \[
--   S(n)=\frac{\exp(r_n+r_n^2/2+r_n^3/6)}{r_n^n\sqrt{2\pi B(r_n)}}.
--   \]
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/Blocks3RealSaddle.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3HAdmissible
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
# Set partitions into blocks of size ≤ 3: the Moser–Wyman real saddle asymptotic

`blocks3_count_over_factorial_isEquivalent_saddle` (Blocks3HAdmissible) gives the abstract H-admissible
saddle estimate for the number of set partitions of `[n]` into blocks of size 1, 2, or 3 (EGF
`exp(z + z²/2 + z³/6)`).  This file realifies the abstract scale to the Moser–Wyman formula

  `B₃(n) / n! ~ exp(r_n + r_n²/2 + r_n³/6) / ( r_n^n · √(2π · (r_n + 2r_n² + 3r_n³/2)) )`,
  `r_n + r_n² + r_n³/2 = n`.

"Unfold and realify" of `saddleScale`, mirroring `BellRealSaddle` / `InvolutionRealSaddle`.
-/

noncomputable section

open Filter Asymptotics
open scoped Topology Real

namespace Blocks3HAdmissible

/-- The Moser–Wyman real saddle scale for blocks-of-size-≤3 partitions. -/
noncomputable def blocks3RealSaddleScale (n : ℕ) : ℝ :=
  Real.exp (blocks3SaddleRadius n + (blocks3SaddleRadius n) ^ 2 / 2
      + (blocks3SaddleRadius n) ^ 3 / 6) /
    ((blocks3SaddleRadius n) ^ n *
      Real.sqrt (2 * Real.pi * blocks3SaddleBReal (blocks3SaddleRadius n)))

end Blocks3HAdmissible


