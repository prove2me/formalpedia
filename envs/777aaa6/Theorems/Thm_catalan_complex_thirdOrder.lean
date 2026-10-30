-- Prove2me | Theorems.Thm_catalan_complex_thirdOrder
-- name    : catalan_complex_thirdOrder
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-25T18:50:41.849772+00:00
-- url     : https://prove2.me/theorems/ebf45e5d-079b-4f4e-8981-19232b776bf4
-- title:
--   Three-term asymptotics of the Catalan numbers
-- statement:
--   Let $C_n$ be the natural Catalan number, with $C_0=1$. As the natural index $n\to\infty$,
--
--   $$C_n=\frac{4^n}{\sqrt\pi}\left(n^{-3/2}-\frac98n^{-5/2}+\frac{145}{128}n^{-7/2}\right)+o\!\left(4^n n^{-7/2}\right).$$
--
--   The formal statement casts $C_n$ into $\mathbb C$, forms the displayed powers of $n$ in $\mathbb R$ and then embeds them in $\mathbb C$. Its real error scale is the norm of $4^n\,\mathrm{ofReal}(n^{-7/2})$. There are no public parameters or assumptions. This is an eventual expansion, not a finite-index identity at $n=0$. It concerns the actual Catalan sequence; no additional tree-type cardinality equivalence is asserted.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/CatalanThirdOrder.lean#L527. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_CatalanThirdOrder
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Third-order Catalan asymptotics

This file proves the three-term Catalan asymptotic by combining the committed
third-order model coefficient estimate with the exact central-binomial bridge.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

theorem catalan_complex_thirdOrder :
    (fun n : ℕ =>
      (catalan n : ℂ) -
        (4 : ℂ) ^ n *
          (((catalanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
              catalanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
              catalanThirdAsymptoticConstant * (n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop]
        (fun n : ℕ =>
          ‖(4 : ℂ) ^ n *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ)‖) := by sorry
