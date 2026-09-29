-- Prove2me | Theorems.Thm_Zeta23_WeilEF_Cf_ne_zero
-- name    : Zeta23.WeilEF.Cf_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:47:45.336765+00:00
-- url     : https://prove2.me/theorems/53b1faac-364b-41f3-aeb9-0006d9664ba1
-- title:
--   Nonvanishing of the zero-free factor $C_f$ on the closed disc of radius $r$
-- statement:
--   Let $f : \mathbb{C} \to \mathbb{C}$ be analytic on a neighbourhood of the closed unit disc $\overline{B}(0,1)$ with $f(0) \ne 0$, and suppose its zero set in the closed unit disc, $\{\rho : \|\rho\| \le 1,\ f(\rho) = 0\}$ (the project's `SetOfZeros 1 f`), is finite. For $r < 1$, let $C_f = $ `Cf r f` be the zero-free factor obtained by dividing out of $f$ the zeros $\rho$ with $\|\rho\| \le r$, each with its analytic multiplicity: away from the zeros, $C_f(z) = f(z) / \prod_{\rho} (z-\rho)^{m_\rho}$, and at a zero $z$ itself the removable singularity is filled in using the local factorization $f = (\cdot - z)^{m_z} g$ with $g(z) \ne 0$.
--
--   The theorem asserts that this factor has no zeros left in the closed disc of radius $r$:
--   $$\|z\| \le r \;\Longrightarrow\; C_f(z) \ne 0.$$
--
--   This is a step in the Landau/Borel–Carathéodory analysis of the module `Zeta23.WeilEF.Landau`: with $C_f$ nonvanishing, its logarithm is analytic on the disc and its logarithmic derivative can be bounded. It feeds `Zeta23.WeilEF.logDeriv_split` (the decomposition $f'/f = \sum_\rho m_\rho/(z-\rho) + C_f'/C_f$) and `Zeta23.WeilEF.norm_logDeriv_Cf_le`, which underlie the bounds on $\zeta'/\zeta$ used in the contour-integration proof of the Weil explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/Landau.lean#L29-L57

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

theorem Zeta23.WeilEF.Cf_ne_zero {f : ℂ → ℂ} (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf0 : f 0 ≠ 0) {r : ℝ} (hr1 : r < 1) (hfin : (SetOfZeros 1 f).Finite)
    {z : ℂ} (hz : ‖z‖ ≤ r) : Cf r f z ≠ 0 := by sorry
