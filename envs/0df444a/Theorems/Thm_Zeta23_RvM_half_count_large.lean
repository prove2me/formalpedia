-- Prove2me | Theorems.Thm_Zeta23_RvM_half_count_large
-- name    : Zeta23.RvM.half_count_large
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:40:38.048322+00:00
-- url     : https://prove2.me/theorems/e97c2482-00b3-45ed-8201-edbe659ff660
-- title:
--   Unit-window count of zeros with $\beta \ge 1/2$ is $O(\log|t|)$
-- statement:
--   **Setup.** For $t \in \mathbb{R}$, let $N_{1/2}(t)$ (`NhalfR t`) be the number of nontrivial zeros $\rho$ of $\zeta$ with $t < \mathrm{Im}\,\rho \le t + 1$ and $\mathrm{Re}\,\rho \ge 1/2$, counted with multiplicity: the finite sum $\sum_\rho m_\rho$ over the window $(t, t+1]$ of the canonical zero configuration, where $m_\rho$ = `zeroMult ρ` is the order of vanishing of $\zeta$ at $\rho$, the sum taken in $\mathbb{R}$.
--
--   **Statement.** There exists a constant $A_1$ such that for every real $t$ with $|t| \ge 4$,
--
--   $$N_{1/2}(t) \;\le\; A_1 \log\bigl(|t| + 3\bigr).$$
--
--   The proof is the classical disc argument: recenter via the affine map so the window lies in a disc around $2 + it$ where $\zeta$ is bounded and $|\zeta(2+it)|$ is bounded below (using $\|\zeta(s) - 1\| \le \pi^2/6 - 1$ on $\mathrm{Re}\,s \ge 2$), and apply Jensen's inequality; multiplicities are transported through the rescaling by `Zeta23.RvM.analyticOrderNatAt_gfun`.
--
--   **Role.** In `Zeta23.RvM.LocalCount` this is half of the local zero-count bound $N(t+1) - N(t) \ll \log(|t|+3)$: by the functional-equation symmetry $\rho \mapsto 1 - \bar\rho$ the $\beta \ge 1/2$ count controls the full count. Consumed by `Zeta23.RvM.zeta_local_zero_count`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/LocalCount.lean#L95-L252

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
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_RvM_LocalCount
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect

open Complex Set Filter Topology Metric
open Zeta23
open Zeta23.RvM

theorem Zeta23.RvM.half_count_large :
    ∃ A₁ : ℝ, ∀ t : ℝ, 4 ≤ |t| → NhalfR t ≤ A₁ * Real.log (|t| + 3) := by sorry
