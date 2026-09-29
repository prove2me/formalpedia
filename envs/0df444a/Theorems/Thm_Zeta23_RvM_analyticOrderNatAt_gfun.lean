-- Prove2me | Theorems.Thm_Zeta23_RvM_analyticOrderNatAt_gfun
-- name    : Zeta23.RvM.analyticOrderNatAt_gfun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:38:09.476683+00:00
-- url     : https://prove2.me/theorems/4c7f1c4e-e48f-4aaa-ac4f-80692b5654f9
-- title:
--   Order transport: the analytic order of $z \mapsto \zeta(s_0 + cz)\,u$ equals the multiplicity of $\zeta$
-- statement:
--   **Setup.** For complex parameters $s_0, c, u$, let $g(z) = \zeta(s_0 + c z)\cdot u$ (the rescaled function `gfun` used in the local zero-count disc argument). `analyticOrderNatAt f w` is Mathlib's $\mathbb{N}$-valued order of vanishing of $f$ at $w$ (the `toNat` of the $\mathbb{N}\cup\{\infty\}$-valued `analyticOrderAt`, with junk value $0$ when $f$ is not analytic at $w$), and `zeroMult ρ` is the project's multiplicity $m_\rho = (\operatorname{analyticOrderAt}\ \zeta\ \rho).\mathrm{toNat}$ of the Riemann zeta function at $\rho$.
--
--   **Statement.** If $c \ne 0$, $u \ne 0$, and $s_0 + c w \ne 1$, then
--
--   $$\operatorname{ord}_{w} \bigl(z \mapsto \zeta(s_0 + c z)\, u\bigr) \;=\; m_{s_0 + c w},$$
--
--   i.e. the order of vanishing of $g$ at $w$ equals the multiplicity of $\zeta$ at the image point $s_0 + c w$: multiplying by a nonzero constant and precomposing with an invertible affine map preserves the analytic order.
--
--   **Role.** In `Zeta23.RvM.LocalCount` this transports zero counts through the affine change of variable that recenters a window of the critical strip onto a disc; it feeds `Zeta23.RvM.half_count_large`, the Jensen-disc bound on the number of zeros with $\beta \ge 1/2$ in a unit window.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/LocalCount.lean#L62-L78

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

theorem Zeta23.RvM.analyticOrderNatAt_gfun {s₀ c u w : ℂ} (hc : c ≠ 0) (hu : u ≠ 0) (h : s₀ + c * w ≠ 1) :
    analyticOrderNatAt (gfun s₀ c u) w = zeroMult (s₀ + c * w) := by sorry
