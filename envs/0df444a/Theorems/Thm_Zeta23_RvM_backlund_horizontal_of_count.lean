-- Prove2me | Theorems.Thm_Zeta23_RvM_backlund_horizontal_of_count
-- name    : Zeta23.RvM.backlund_horizontal_of_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:38:49.284596+00:00
-- url     : https://prove2.me/theorems/0ac15f18-6580-4b54-981f-69b969f105c2
-- title:
--   Backlund's horizontal bound from the zero count of $\mathrm{Re}\,\zeta$
-- statement:
--   **Setup.** For $T \in \mathbb{R}$ let $\mathrm{reZeroSet}(T) = \{\sigma \in [1/2, 2] : \mathrm{Re}\,\zeta(\sigma + iT) = 0\}$. A nontrivial zero of $\zeta$ is a $\rho$ with $\zeta(\rho) = 0$ and $0 < \mathrm{Re}\,\rho < 1$.
--
--   **Statement.** Assume the zero-count input (J): there exist $C$ and $T_0$ such that for all $T \ge T_0$ the set $\mathrm{reZeroSet}(T)$ is finite with $\#\,\mathrm{reZeroSet}(T) \le C \log T$. Then there exist $C'$ and $T_0'$ such that for all $T \ge T_0'$ at which no nontrivial zero of $\zeta$ has ordinate $T$,
--
--   $$\Bigl|\,\mathrm{Im} \int_{1/2}^{2} \frac{\zeta'}{\zeta}(\sigma + iT)\, d\sigma\,\Bigr| \;\le\; C' \log T.$$
--
--   This is Backlund's classical bound on the argument variation of $\zeta$ along the horizontal segment from $\tfrac12 + iT$ to $2 + iT$, derived from a bound on the number of sign changes of $\mathrm{Re}\,\zeta$ on that segment.
--
--   **Role.** In the Riemann–von Mangoldt development (`Zeta23.RvM.Backlund`), this converts the Jensen-type count `Zeta23.RvM.reZeroSet_card_le_of_growth` into the $O(\log T)$ bound on the horizontal piece of the contour; it is consumed directly by the main Riemann–von Mangoldt theorem `Zeta23.RvM.rvM_main`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/Backlund.lean#L318-L326

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
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
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
import Definitions.Def_Zeta23_RvM_BacklundDefs
import Definitions.Def_Zeta23_Statement

open Complex Set MeasureTheory Real intervalIntegral
attribute [-instance] LieAlgebra.ofAssociativeAlgebra
open Zeta23
open RvM

theorem Zeta23.RvM.backlund_horizontal_of_count
    (hJ : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (reZeroSet T).Finite ∧ ((reZeroSet T).ncard : ℝ) ≤ C * Real.log T) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ C * Real.log T := by sorry
