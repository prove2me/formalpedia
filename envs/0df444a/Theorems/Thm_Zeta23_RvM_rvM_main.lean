-- Prove2me | Theorems.Thm_Zeta23_RvM_rvM_main
-- name    : Zeta23.RvM.rvM_main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:42:41.698797+00:00
-- url     : https://prove2.me/theorems/0a8f5660-7f33-4ee9-8a65-e659a815076a
-- title:
--   Riemann-von Mangoldt formula: $N(T,2T) = \frac{T}{2\pi}\,\ell_1(T) + O(\log T)$
-- statement:
--   Let $N(T, 2T)$ denote the number of nontrivial zeros $\rho$ of the Riemann zeta function with imaginary part in the window $T < \operatorname{Im}\rho \le 2T$, counted with multiplicity (the analytic order of vanishing of Mathlib's `riemannZeta`); formally this is `zetaZeroConfig.N T (2*T)`. Write $\ell_1(T) := \log\frac{T}{2\pi} + 2\log 2 - 1$.
--
--   **Statement.** Assuming the Stirling-type facts for the archimedean density $\mu$ bundled in the hypothesis `GammaFacts` (H-$\Gamma$; proved elsewhere in the repository), there exist constants $C$ and $T_0$ such that for all $T \ge T_0$,
--   $$\Bigl|\,N(T, 2T) \;-\; \frac{T}{2\pi}\,\ell_1(T)\,\Bigr| \;\le\; C \log T.$$
--
--   This is the dyadic-window form of the classical Riemann-von Mangoldt formula [Tit86, Thm 9.4]. In the project it is one of the two zero-counting inputs to the endgame: it normalizes the denominator $N(T,2T)$ in Theorem A, and it is consumed directly by `Zeta23.thmA0_cumulative` and `Zeta23.thmA1`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/MainTerm.lean#L479-L484, docstring tag [Tit86, Thm 9.4]

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect

open Complex MeasureTheory
attribute [-instance] LieAlgebra.ofAssociativeAlgebra
open Zeta23
set_option maxHeartbeats 1000000

theorem Zeta23.RvM.rvM_main (hΓ : GammaFacts) : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(zetaZeroConfig.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T| ≤ C * Real.log T := by sorry
