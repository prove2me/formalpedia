-- Prove2me | Theorems.Thm_InvolutionHAdmissible_involution_count_over_factorial_isEquivalent_real_saddle
-- name    : InvolutionHAdmissible.involution_count_over_factorial_isEquivalent_real_saddle
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-27T23:02:47.253609+00:00
-- url     : https://prove2.me/theorems/caf00866-9a47-4a3c-ba54-601636e104a7
-- title:
--   A real saddle equivalent for the source size-one-or-two block model
-- statement:
--   Let $a_n=\texttt{involCoeffR}(n)$ be the EGF coefficient of the source labelled-set class `parts12.set`, normalized by $n!$, and put $r_n=(\sqrt{1+4n}-1)/2$. Then $$a_n\sim\frac{\exp(r_n+r_n^2/2)}{r_n^n\sqrt{2\pi(r_n+2r_n^2)}}.$$ The theorem uses the literal labelled-set class and does not itself identify its objects with a separate permutation-involution datatype.
--
--   The local source models, scales or predicates are defined exactly by:
--
--   ```lean
--   noncomputable def involRealSaddleScale (n : ℕ) : ℝ :=
--     Real.exp (involSaddleRadius n + (involSaddleRadius n) ^ 2 / 2) /
--       ((involSaddleRadius n) ^ n *
--         Real.sqrt (2 * Real.pi * involSaddleBReal (involSaddleRadius n)))
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/InvolutionRealSaddle.lean#L88. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Poles
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SubstComp
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bound
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpStirling
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_GaussianMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Fibonacci
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_SequenceInverse
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledProduct
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Exp
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_GaussianCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_HAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledPower
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSetOde
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bell
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSeq
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_BellHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionRealSaddle
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionThirdOrder
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

open Filter Asymptotics
open scoped Topology Real

open InvolutionHAdmissible

theorem InvolutionHAdmissible.involution_count_over_factorial_isEquivalent_real_saddle :
    (fun n : ℕ => involCoeffR n) ~[atTop] involRealSaddleScale := by sorry
