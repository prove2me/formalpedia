-- Prove2me | Theorems.Thm_Zeta23_WeilEF_finite_SetOfZeros
-- name    : Zeta23.WeilEF.finite_SetOfZeros
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:49:14.047216+00:00
-- url     : https://prove2.me/theorems/41946136-8984-40f8-bb1b-ccc70838608c
-- title:
--   Finiteness of the zero set of an analytic function in the closed unit ball
-- statement:
--   For $R > 0$ and $f : \mathbb{C} \to \mathbb{C}$, write $\operatorname{SetOfZeros}(R, f) = \{\rho \in \mathbb{C} : \|\rho\| \le R,\ f(\rho) = 0\}$ for the zero set of $f$ in the closed ball of radius $R$ about the origin.
--
--   Suppose $f$ is analytic on a neighbourhood of the closed unit ball $\overline{B}(0,1)$ (hypothesis `AnalyticOnNhd`) and $f(0) \ne 0$. Then
--   $$\operatorname{SetOfZeros}(1, f) \text{ is finite.}$$
--   Since $f(0) \ne 0$, $f$ is not identically zero, so by the identity theorem its zeros are isolated; a compactness argument on $\overline{B}(0,1)$ then yields finiteness.
--
--   This is a preparatory step for the Landau-type partial-fraction decomposition `logDeriv_partial_fraction_disk`, which expresses $f'/f$ as a finite sum over these zeros plus a controlled error, and which ultimately feeds the "good heights" bounds on $\zeta'/\zeta$ used in the Weil explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/Landau.lean#L313-L342

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

theorem Zeta23.WeilEF.finite_SetOfZeros {f : ℂ → ℂ}
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0 : f 0 ≠ 0) :
    (SetOfZeros 1 f).Finite := by sorry
