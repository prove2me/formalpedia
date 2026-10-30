-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_BellRealSaddle
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_BellRealSaddle
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T23:07:56.313506+00:00
-- url     : https://prove2.me/theorems/2bd2de39-96d2-44aa-9f8c-dd21df290ad5
-- title:
--   Bell Real Saddle
-- statement:
--   The source mathematical objects and operations are specified by the following definitions.
--
--   ```lean
--   noncomputable def bellRealSaddleScale (n : ℕ) : ℝ :=
--     Real.exp (Real.exp (bellSaddleRadius n) - 1) /
--       (bellSaddleRadius n ^ n *
--         Real.sqrt (2 * Real.pi * bellSaddleBReal (bellSaddleRadius n)))
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/BellRealSaddle.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_BellHAdmissible
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
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Bell numbers: the classical Moser–Wyman real saddle asymptotic

`bell_number_over_factorial_isEquivalent_saddle` (BellHAdmissible) gives the H-admissible saddle
estimate `B_n/n! ~ saddleScale …` with a complex `saddleScale`.  This file realifies that abstract
scale to the recognizable Moser–Wyman formula

  `B_n / n! ~ exp(e^{r_n} − 1) / ( r_n^n · √(2π · r_n(r_n+1) e^{r_n}) )`,   `r_n e^{r_n} = n`,

where `r_n = bellSaddleRadius n` and `r_n(r_n+1)e^{r_n} = bellSaddleBReal (bellSaddleRadius n)`.
The content is an "unfold and realify" of `saddleScale` (all factors are real and positive for `n ≥ 1`),
transported back through `ofReal_isEquivalent_iff`.
-/

noncomputable section

open Filter Asymptotics
open scoped Topology Real

/-- The classical real Moser–Wyman Bell saddle scale. -/
noncomputable def bellRealSaddleScale (n : ℕ) : ℝ :=
  Real.exp (Real.exp (bellSaddleRadius n) - 1) /
    (bellSaddleRadius n ^ n *
      Real.sqrt (2 * Real.pi * bellSaddleBReal (bellSaddleRadius n)))


