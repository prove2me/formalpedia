-- Prove2me | Theorems.Thm_bell_number_over_factorial_thirdOrder
-- name    : bell_number_over_factorial_thirdOrder
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:53:35.374464+00:00
-- url     : https://prove2.me/theorems/8def7cc0-34fa-4e46-b8b6-1fd67d9d196c
-- title:
--   Bell coefficient ratio with explicit saddle corrections
-- statement:
--   Let $B_n=\mathrm{CombClass.posInt.set.counts}(n)$ be the source's set-partition count and $f(z)=\exp(\exp z-1)$. Let $r_n\ge0$ be the chosen real solution of $r_ne^{r_n}=n$. Put
--
--   $$b(r)=r(r+1)e^r,\qquad S_n=\frac{\exp(e^{r_n}-1)}{r_n^n\sqrt{2\pi b(r_n)}}.$$
--
--   Define
--
--   $$b_3(r)=(r+3r^2+r^3)e^r,\quad b_4(r)=(r+7r^2+6r^3+r^4)e^r,$$
--   $$b_5(r)=(r+15r^2+25r^3+10r^4+r^5)e^r,$$
--   $$b_6(r)=(r+31r^2+90r^3+65r^4+15r^5+r^6)e^r.$$
--
--   Using the corrections
--
--   $$d_1(r)=\frac{b_4(r)}{8b(r)^2}-\frac{5b_3(r)^2}{24b(r)^3},\qquad d_2(r)=-\frac{b_6(r)}{48b(r)^3}+\frac{7b_3(r)b_5(r)}{48b(r)^4}+\frac{35b_4(r)^2}{384b(r)^4}-\frac{35b_3(r)^2b_4(r)}{64b(r)^5}+\frac{385b_3(r)^4}{1152b(r)^6},$$
--
--   and the actual robust scale
--
--   $$c(r)=\frac{|b_4(r)|}{b(r)^2}+\frac{b_3(r)^2}{b(r)^3},$$
--
--   the source proves
--
--   $$\frac{B_n}{n!\,S_n}-\bigl(1+d_1(r_n)+d_2(r_n)\bigr)=o(c(r_n)).$$
--
--   There are no public hypotheses: the named Bell constructions supply the admissibility and local/tail estimates. Factorial normalization is retained. In this theorem $\mathrm{bellThirdCorrScale}=\mathrm{bellSecondCorrScale}=c$ exactly; the additional correction does not assert a sharper third-order error scale. The statement uses the actual decorated-partition class, with no invented bridge to a separate $\mathrm{Nat.bell}$ symbol. It is an eventual asymptotic, not a finite-index ratio formula at $n=0$.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/BellThirdOrder.lean#L1411. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_BellThirdOrder
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
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
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Third-order saddle data for Bell numbers

This file instantiates the third-order Hayman wrapper for
`exp (exp z - 1)`.  The fifth and sixth logarithmic saddle derivatives are
the next two Touchard polynomials evaluated at the Bell saddle.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem bell_number_over_factorial_thirdOrder :
    (fun n : ℕ =>
      (((AnalyticCombinatorics.Ch1.CombClass.posInt.set.counts n : ℝ) /
          n.factorial : ℝ) : ℂ) / bellSecondOrderSaddleScale n -
        (1 + (saddleCorrection bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
          (bellSaddleRadius n) : ℂ) +
          (saddleThirdCorrection bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
            bellSaddleB5Real bellSaddleB6Real (bellSaddleRadius n) : ℂ)))
      =o[atTop]
    (fun n : ℕ => (bellThirdCorrScale (bellSaddleRadius n) : ℂ)) := by sorry
