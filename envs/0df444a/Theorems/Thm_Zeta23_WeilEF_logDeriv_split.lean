-- Prove2me | Theorems.Thm_Zeta23_WeilEF_logDeriv_split
-- name    : Zeta23.WeilEF.logDeriv_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:49:19.551409+00:00
-- url     : https://prove2.me/theorems/df96217f-6605-40ce-84a0-a4fb776d427d
-- title:
--   Splitting $f'/f$ into the zero sum plus the log-derivative of the zero-free part
-- statement:
--   Setup. Let $f : \mathbb{C} \to \mathbb{C}$ be analytic on a neighbourhood of the closed unit ball $\overline{B}(0,1)$ with $f(0) \ne 0$, and suppose the zero set $\operatorname{SetOfZeros}(1, f) = \{\rho : \|\rho\| \le 1,\ f(\rho) = 0\}$ is finite. Fix $r < 1$; the zeros with $\|\rho\| \le r$ then form a finite set (`finiteSetOfZeros_mono`). Write $m_\rho = \operatorname{analyticOrderNatAt} f\,\rho$ for the order of vanishing of $f$ at $\rho$, and let $C_f(r, f)$ (the definition `Cf`) be the "zero-free part" of $f$ at radius $r$: $f$ divided by the product $\prod_\rho (z - \rho)^{m_\rho}$ over the zeros in $\overline{B}(0,r)$, defined so as to be analytic and nonvanishing where $f$'s zeros have been removed.
--
--   Assertion. For every $z$ with $\|z\| < r$ and $f(z) \ne 0$,
--   $$\frac{f'}{f}(z) \;=\; \sum_{\rho\,:\,\|\rho\| \le r,\ f(\rho) = 0} \frac{m_\rho}{z - \rho} \;+\; \frac{C_f'}{C_f}(z),$$
--   where the sum runs over the finite set of zeros of $f$ in the closed ball of radius $r$.
--
--   This is the algebraic core of the Landau partial-fraction machinery: separating the singular zero contributions from a regular remainder whose logarithmic derivative can then be bounded by Borel-Caratheodory-type estimates. It is consumed by `logDeriv_partial_fraction_disk`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/Landau.lean#L86-L124

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

theorem Zeta23.WeilEF.logDeriv_split {f : ℂ → ℂ} (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf0 : f 0 ≠ 0) {r : ℝ} (hr1 : r < 1) (hfin : (SetOfZeros 1 f).Finite)
    {z : ℂ} (hz : ‖z‖ < r) (hfz : f z ≠ 0) :
    logDeriv f z = (∑ ρ ∈ (finiteSetOfZeros_mono hr1 hfin).toFinset,
        (analyticOrderNatAt f ρ : ℂ) / (z - ρ)) + logDeriv (Cf r f) z := by sorry
