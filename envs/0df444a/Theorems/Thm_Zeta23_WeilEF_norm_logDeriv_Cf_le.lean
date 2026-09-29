-- Prove2me | Theorems.Thm_Zeta23_WeilEF_norm_logDeriv_Cf_le
-- name    : Zeta23.WeilEF.norm_logDeriv_Cf_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:50:01.42657+00:00
-- url     : https://prove2.me/theorems/f0d37c0c-8856-4368-bbe2-0f4e9cc14cf9
-- title:
--   Borel–Carathéodory bound for the logarithmic derivative of the zero-free factor
-- statement:
--   Let $f : \mathbb{C} \to \mathbb{C}$ be analytic on a neighbourhood of the closed unit disc with $f(0) = 1$, and assume its zero set in the closed unit disc is finite. Let $B \ge 2$ satisfy $\|f(w)\| \le B$ for $\|w\| \le 24/25$. Here `Cf (22/25) f` denotes the *regular part* of $f$: $f$ divided by $\prod_\rho (z - \rho)^{m_\rho}$, the product running over the zeros $\rho$ of $f$ with $\|\rho\| \le 22/25$ counted with their analytic orders $m_\rho$ (with the removable values at the zeros themselves filled in), so that the quotient is analytic and zero-free on the smaller disc.
--
--   **Statement.** For every $z$ with $\|z\| \le 83/100$,
--   $$\Bigl\| \frac{d}{dz} \log \mathrm{Cf}(22/25, f)(z) \Bigr\| \le 44795000 \, \log B.$$
--   This is a fully explicit Landau/Borel–Carathéodory-type lemma: the logarithmic derivative of the zero-free factor of a bounded analytic function is controlled by $\log B$ on a strictly smaller disc, with the concrete radii $22/25 < 83/100 < 24/25 < 1$ and the explicit constant $44795000$.
--
--   **Role.** In the module `Zeta23.WeilEF.Landau` it is the engine behind `logDeriv_partial_fraction_disk`, which in turn yields the partial-fraction expansion of $\zeta'/\zeta$ near height $t$ used for the good-heights contour argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/Landau.lean#L126-L294

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
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
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix

open Complex Set
open Metric

theorem Zeta23.WeilEF.norm_logDeriv_Cf_le {f : ℂ → ℂ} {B : ℝ}
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0 : f 0 = 1)
    (hfin : (SetOfZeros 1 f).Finite) (hB2 : 2 ≤ B)
    (hfB : ∀ w : ℂ, ‖w‖ ≤ 24/25 → ‖f w‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ 83/100) :
    ‖logDeriv (Cf (22/25) f) z‖ ≤ 44795000 * Real.log B := by sorry
